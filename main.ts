// png-squeeze — a lossless PNG squeezer for 1280x720 screenshots.
//
// Pipeline per image: decode to RGBA, survey the pixels, try the colour
// forms the image allows (palette / grey / grey+alpha / RGB / RGBA, plus a
// tRNS-keyed form when exactly one value is ever fully transparent), filter
// each form's rows several ways, screen the candidates with zlib level 6,
// then squeeze the survivors with a hand-rolled optimal-parsing deflate and
// keep whichever stream — ours or zlib level 9 — is smaller.
//
// Everything is budgeted by work, never by the clock: fixed block sizes,
// fixed chain limits, fixed iteration counts. No Date, no randomness, no
// environment reads beyond the input/output directory overrides, so two
// runs over the same inputs produce byte-identical files.
import { chmodSync, mkdirSync, readdirSync, readFileSync, statSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { deflateSync, inflateSync } from 'node:zlib';

// ---------------------------------------------------------------- checksums

// CRC-32 (IEEE) lookup table, built once at load.
const CRC32_TABLE = (() => {
  const table = new Int32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    table[n] = c;
  }
  return table;
})();

// CRC-32 of bytes[start, end).
function crc32Range(bytes, start, end) {
  let c = -1;
  for (let i = start; i < end; i++) c = CRC32_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8);
  return (c ^ -1) >>> 0;
}

// Adler-32 of a whole buffer, in 5552-byte blocks to stay in range.
function adler32Of(bytes) {
  let a = 1;
  let b = 0;
  for (let i = 0; i < bytes.length; ) {
    const end = Math.min(bytes.length, i + 5552);
    for (; i < end; i++) {
      a += bytes[i];
      b += a;
    }
    a %= 65521;
    b %= 65521;
  }
  return ((b << 16) | a) >>> 0;
}

// ---------------------------------------------------------------- PNG decode

const PNG_SIGNATURE = [137, 80, 78, 71, 13, 10, 26, 10];
const SAMPLES_PER_PIXEL = { 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 };

// The Paeth predictor: whichever of left / above / above-left the linear
// prediction p = a + b - c is closest to.
function paethPredictor(left, above, aboveLeft) {
  const p = left + above - aboveLeft;
  const pa = p > left ? p - left : left - p;
  const pb = p > above ? p - above : above - p;
  const pc = p > aboveLeft ? p - aboveLeft : aboveLeft - p;
  if (pa <= pb && pa <= pc) return left;
  return pb <= pc ? above : aboveLeft;
}

// Split a PNG file into its parts, checking every chunk CRC on the way.
// Returns the header, palette / tRNS data when present, and the IDAT pieces.
function parsePngChunks(bytes) {
  if (bytes.length < 8 || PNG_SIGNATURE.some((v, i) => bytes[i] !== v)) throw new Error('not a PNG');
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = 8;
  let header = null;
  let palette = null;
  let trns = null;
  const idat = [];
  let ended = false;
  while (at < bytes.length) {
    if (at + 12 > bytes.length) throw new Error('truncated chunk');
    const len = view.getUint32(at);
    if (at + 12 + len > bytes.length) throw new Error('chunk overruns file');
    const type = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]);
    if (crc32Range(bytes, at + 4, at + 8 + len) !== view.getUint32(at + 8 + len)) throw new Error('bad CRC in ' + type);
    const data = bytes.subarray(at + 8, at + 8 + len);
    at += 12 + len;
    if (type === 'IHDR') {
      const dv = new DataView(data.buffer, data.byteOffset, 13);
      header = { width: dv.getUint32(0), height: dv.getUint32(4), depth: data[8], colourType: data[9], interlace: data[12] };
      if (header.depth !== 8 || header.interlace !== 0 || !Object.hasOwn(SAMPLES_PER_PIXEL, header.colourType)) throw new Error('unsupported IHDR');
    } else if (type === 'PLTE') palette = data;
    else if (type === 'tRNS') trns = data;
    else if (type === 'IDAT') idat.push(data);
    else if (type === 'IEND') {
      ended = true;
      break;
    } else throw new Error('unexpected chunk ' + type);
  }
  if (!ended || !header || idat.length === 0) throw new Error('incomplete PNG');
  return { header, palette, trns, idat };
}

// Undo the per-row filters of an inflated scanline buffer (filter byte +
// stride bytes per row) back to plain samples.
function unfilterScanlines(raw, width, height, bpp) {
  const stride = width * bpp;
  const samples = new Uint8Array(height * stride);
  for (let y = 0; y < height; y++) {
    const filter = raw[y * (stride + 1)];
    if (filter > 4) throw new Error('bad filter type');
    const src = y * (stride + 1) + 1;
    const o = y * stride;
    const p = o - stride;
    if (filter === 0) samples.set(raw.subarray(src, src + stride), o);
    else if (filter === 1) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (i >= bpp ? samples[o + i - bpp] : 0);
    } else if (filter === 2) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (y > 0 ? samples[p + i] : 0);
    } else if (filter === 3) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (((i >= bpp ? samples[o + i - bpp] : 0) + (y > 0 ? samples[p + i] : 0)) >> 1);
    } else {
      for (let i = 0; i < stride; i++) {
        const a = i >= bpp ? samples[o + i - bpp] : 0;
        const b = y > 0 ? samples[p + i] : 0;
        const c = y > 0 && i >= bpp ? samples[p + i - bpp] : 0;
        samples[o + i] = raw[src + i] + paethPredictor(a, b, c);
      }
    }
  }
  return samples;
}

// Expand decoded samples of any supported colour type to RGBA pixels.
function expandSamplesToRgba(samples, width, height, colourType, palette, trns) {
  const n = width * height;
  const rgba = new Uint8Array(n * 4);
  if (colourType === 6) rgba.set(samples);
  else if (colourType === 2) {
    const key = trns === null ? -1 : (trns[1] << 16) | (trns[3] << 8) | trns[5];
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 3, d += 4) {
      rgba[d] = samples[s];
      rgba[d + 1] = samples[s + 1];
      rgba[d + 2] = samples[s + 2];
      rgba[d + 3] = ((samples[s] << 16) | (samples[s + 1] << 8) | samples[s + 2]) === key ? 0 : 255;
    }
  } else if (colourType === 0) {
    const key = trns === null ? -1 : trns[1];
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const g = samples[i];
      rgba[d] = rgba[d + 1] = rgba[d + 2] = g;
      rgba[d + 3] = g === key ? 0 : 255;
    }
  } else if (colourType === 4) {
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 2, d += 4) {
      rgba[d] = rgba[d + 1] = rgba[d + 2] = samples[s];
      rgba[d + 3] = samples[s + 1];
    }
  } else {
    const entries = palette.length / 3;
    const lut = new Uint8Array(entries * 4);
    for (let e = 0; e < entries; e++) {
      lut[e * 4] = palette[e * 3];
      lut[e * 4 + 1] = palette[e * 3 + 1];
      lut[e * 4 + 2] = palette[e * 3 + 2];
      lut[e * 4 + 3] = trns !== null && e < trns.length ? trns[e] : 255;
    }
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const e = samples[i];
      rgba[d] = lut[e * 4];
      rgba[d + 1] = lut[e * 4 + 1];
      rgba[d + 2] = lut[e * 4 + 2];
      rgba[d + 3] = lut[e * 4 + 3];
    }
  }
  return rgba;
}

// Decode any 8-bit non-interlaced PNG of colour type 0/2/3/4/6 to RGBA.
function readPngToRgba(bytes) {
  const { header, palette, trns, idat } = parsePngChunks(bytes);
  const { width, height, colourType } = header;
  const bpp = SAMPLES_PER_PIXEL[colourType];
  const stride = width * bpp;
  const expected = height * (stride + 1);
  const raw = inflateSync(Buffer.concat(idat), { maxOutputLength: expected + 1 });
  if (raw.length !== expected) throw new Error('IDAT inflates to the wrong size');
  const samples = unfilterScanlines(raw, width, height, bpp);
  return { width, height, rgba: expandSamplesToRgba(samples, width, height, colourType, palette, trns) };
}

// ---------------------------------------------------------------- image survey

// What an image holds: fully opaque? grey only? and its colours, when there
// are at most 256 distinct ones (colours is null once a 257th shows up).
function surveyPixels(rgba) {
  const n = rgba.length >>> 2;
  let opaque = true;
  let grey = true;
  const counts = new Map();
  let many = false;
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    if (rgba[d + 3] !== 255) opaque = false;
    if (rgba[d] !== rgba[d + 1] || rgba[d] !== rgba[d + 2]) grey = false;
    if (!many) {
      const c = (rgba[d] << 24) | (rgba[d + 1] << 16) | (rgba[d + 2] << 8) | rgba[d + 3];
      const k = counts.get(c);
      if (k === undefined) {
        if (counts.size === 256) many = true;
        else counts.set(c, 1);
      } else counts.set(c, k + 1);
    }
  }
  const colours = many
    ? null
    : [...counts.entries()].map(([word, count]) => ({
        rgba: [(word >>> 24) & 255, (word >>> 16) & 255, (word >>> 8) & 255, word & 255],
        word,
        count,
      }));
  return { opaque, grey, colours };
}

// The one fully-transparent value the image could key by tRNS instead of
// carrying an alpha channel, or null. Every pixel must be opaque or exactly
// that value at alpha 0, and no opaque pixel may share the value.
function findTransparentKey(rgba, grey) {
  let key = -1;
  for (let d = 0; d < rgba.length; d += 4) {
    const a = rgba[d + 3];
    if (a === 255) continue;
    if (a !== 0) return null;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (key === -1) key = v;
    else if (key !== v) return null;
  }
  if (key === -1) return null;
  for (let d = 0; d < rgba.length; d += 4) {
    if (rgba[d + 3] !== 255) continue;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (v === key) return null;
  }
  return key;
}

// The image's samples in colour type ct (0, 2, 4 or 6) taken from its RGBA.
function extractSamples(rgba, ct) {
  const n = rgba.length >>> 2;
  if (ct === 6) return rgba;
  const ch = ct === 0 ? 1 : ct === 4 ? 2 : 3;
  const out = new Uint8Array(n * ch);
  for (let i = 0, d = 0, s = 0; i < n; i++, d += 4, s += ch) {
    if (ct === 0) out[s] = rgba[d];
    else if (ct === 4) {
      out[s] = rgba[d];
      out[s + 1] = rgba[d + 3];
    } else {
      out[s] = rgba[d];
      out[s + 1] = rgba[d + 1];
      out[s + 2] = rgba[d + 2];
    }
  }
  return out;
}

// A palette's entries in the order a trial writes them: transparent ones
// first (by alpha), then by count or by luminance.
function orderPaletteEntries(colours, order) {
  const luminance = (c) => 299 * c.rgba[0] + 587 * c.rgba[1] + 114 * c.rgba[2];
  return [...colours].sort((x, y) => {
    const ta = x.rgba[3] === 255 ? 1 : 0;
    const tb = y.rgba[3] === 255 ? 1 : 0;
    if (ta !== tb) return ta - tb;
    if (ta === 0 && x.rgba[3] !== y.rgba[3]) return x.rgba[3] - y.rgba[3];
    if (order === 'luminance') return luminance(x) - luminance(y) || x.word - y.word;
    return y.count - x.count || x.word - y.word;
  });
}

// Build one palette form: PLTE / tRNS chunks plus the per-pixel indices.
function buildPaletteForm(rgba, colours, order) {
  const entries = orderPaletteEntries(colours, order);
  const index = new Map(entries.map((c, i) => [c.word, i]));
  const plte = new Uint8Array(entries.length * 3);
  let transparent = 0;
  entries.forEach((c, i) => {
    plte[i * 3] = c.rgba[0];
    plte[i * 3 + 1] = c.rgba[1];
    plte[i * 3 + 2] = c.rgba[2];
    if (c.rgba[3] !== 255) transparent = i + 1;
  });
  const trns = transparent === 0 ? null : Uint8Array.from(entries.slice(0, transparent), (c) => c.rgba[3]);
  const n = rgba.length >>> 2;
  const indices = new Uint8Array(n);
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    const c = (rgba[d] << 24) | (rgba[d + 1] << 16) | (rgba[d + 2] << 8) | rgba[d + 3];
    indices[i] = index.get(c);
  }
  return { plte, trns, indices };
}

// The filter choices each form is tried with.
const FORM_FILTERS = Object.freeze({
  palette: Object.freeze([0]),
  paletteByLuminance: Object.freeze([0, 'minsum', 'brute']),
  channels: Object.freeze([0, 1, 2, 4, 'minsum', 'pairs', 'brute']),
});

// Every form an image can be written in: palette forms first (when the
// colour count allows), then the single channel form it reduces to.
function candidateForms(rgba) {
  const { opaque, grey, colours } = surveyPixels(rgba);
  const forms = [];
  if (colours !== null) {
    for (const [order, filters] of [
      ['count', FORM_FILTERS.palette],
      ['luminance', FORM_FILTERS.paletteByLuminance],
    ]) {
      const p = buildPaletteForm(rgba, colours, order);
      forms.push({ colourType: 3, bpp: 1, samples: p.indices, plte: p.plte, trns: p.trns, filters });
    }
    if (!grey) return forms;
  }
  const key = opaque ? null : findTransparentKey(rgba, grey);
  let ct;
  let trns = null;
  if (grey) {
    ct = opaque || key !== null ? 0 : 4;
    if (key !== null) trns = Uint8Array.of(0, key);
  } else {
    ct = opaque || key !== null ? 2 : 6;
    if (key !== null) trns = Uint8Array.of(0, key >>> 16, 0, (key >>> 8) & 0xff, 0, key & 0xff);
  }
  const bpp = { 0: 1, 2: 3, 4: 2, 6: 4 }[ct];
  forms.push({ colourType: ct, bpp, samples: extractSamples(rgba, ct), plte: null, trns, filters: FORM_FILTERS.channels });
  return forms;
}

// The bytes a form's PLTE and tRNS chunks add to its file.
const auxChunkBytes = (form) => (form.plte === null ? 0 : 12 + form.plte.length) + (form.trns === null ? 0 : 12 + form.trns.length);

// ---------------------------------------------------------------- row filters

// Apply one PNG row filter to the current row (prev is null on row 0).
function applyFilterRow(type, cur, prev, bpp, out) {
  const n = cur.length;
  if (type === 0) out.set(cur);
  else if (type === 1) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (i >= bpp ? cur[i - bpp] : 0);
  } else if (type === 2) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (prev === null ? 0 : prev[i]);
  } else if (type === 3) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (((i >= bpp ? cur[i - bpp] : 0) + (prev === null ? 0 : prev[i])) >> 1);
  } else {
    for (let i = 0; i < n; i++) {
      const a = i >= bpp ? cur[i - bpp] : 0;
      const b = prev === null ? 0 : prev[i];
      const c = prev !== null && i >= bpp ? prev[i - bpp] : 0;
      out[i] = cur[i] - paethPredictor(a, b, c);
    }
  }
}

// Sum of |signed byte| over a filtered row — the classic cheap filter score.
function signedAbsSum(row) {
  let s = 0;
  for (let i = 0; i < row.length; i++) {
    const v = row[i];
    s += v < 128 ? v : 256 - v;
  }
  return s;
}

// How many distinct adjacent byte pairs a row holds (fewer pairs means more
// repeatable, hence more compressible). `seen`/`stamp` memoise per call.
function countFreshPairs(row, seen, stamp) {
  let n = 0;
  for (let i = 1; i < row.length; i++) {
    const pair = (row[i - 1] << 8) | row[i];
    if (seen[pair] !== stamp) {
      seen[pair] = stamp;
      n++;
    }
  }
  return n;
}

const BRUTE_LOOKBACK = 32768;
const BRUTE_ZLIB_LEVEL = 4;

// The filtered bytes of `samples` under `choice`: a fixed filter 0-4, or a
// per-row heuristic ('minsum' / 'pairs'), or 'brute' — each filter tried per
// row and weighed by a small deflate run over the bytes written before it.
function filterImage(samples, width, height, bpp, choice) {
  const stride = width * bpp;
  const raw = new Uint8Array(height * (stride + 1));
  const trial = Array.from({ length: 5 }, () => new Uint8Array(stride + 1));
  for (let t = 0; t < 5; t++) trial[t][0] = t;
  const seen = new Uint32Array(65536);
  let stamp = 0;
  for (let y = 0; y < height; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    const at = y * (stride + 1);
    if (typeof choice === 'number') {
      raw[at] = choice;
      applyFilterRow(choice, cur, prev, bpp, raw.subarray(at + 1, at + 1 + stride));
      continue;
    }
    const before = raw.subarray(Math.max(0, at - BRUTE_LOOKBACK), at);
    let type = 0;
    let best = Infinity;
    for (let t = 0; t < 5; t++) {
      applyFilterRow(t, cur, prev, bpp, trial[t].subarray(1));
      let cost;
      if (choice === 'minsum') cost = signedAbsSum(trial[t].subarray(1));
      else if (choice === 'pairs') cost = countFreshPairs(trial[t].subarray(1), seen, ++stamp);
      else {
        cost = deflateSync(
          trial[t],
          before.length === 0 ? { level: BRUTE_ZLIB_LEVEL, memLevel: 9 } : { level: BRUTE_ZLIB_LEVEL, memLevel: 9, dictionary: before },
        ).length;
      }
      if (cost < best) {
        best = cost;
        type = t;
      }
    }
    raw.set(trial[type], at);
  }
  return raw;
}

// ---------------------------------------------------------------- deflate

// RFC 1951 length / distance code tables.
const LENGTH_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LENGTH_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
const DISTANCE_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DISTANCE_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];

// Symbol / extra-bit lookups for every length 0..258 and distance 1..32768.
const LENGTH_SYMBOL = new Uint16Array(259);
const LENGTH_EXTRA_BITS = new Uint8Array(259);
for (let s = 0; s < 29; s++) {
  const top = s === 28 ? 258 : LENGTH_BASE[s + 1] - 1;
  for (let l = LENGTH_BASE[s]; l <= top; l++) {
    LENGTH_SYMBOL[l] = 257 + s;
    LENGTH_EXTRA_BITS[l] = LENGTH_EXTRA[s];
  }
}
const DISTANCE_SYMBOL = new Uint16Array(32769);
const DISTANCE_EXTRA_BITS = new Uint8Array(32769);
for (let s = 0; s < 30; s++) {
  const top = s === 29 ? 32768 : DISTANCE_BASE[s + 1] - 1;
  for (let d = DISTANCE_BASE[s]; d <= top; d++) {
    DISTANCE_SYMBOL[d] = s;
    DISTANCE_EXTRA_BITS[d] = DISTANCE_EXTRA[s];
  }
}

// ------------------------------------------------------------ bit writer

// Little-endian bit sink: bits accumulate LSB-first into bytes.
class BitWriter {
  constructor(hint) {
    this.buf = new Uint8Array(Math.max(1024, hint));
    this.pos = 0;
    this.bitBuf = 0;
    this.bitCnt = 0;
  }
  ensure() {
    if (this.pos + 16 > this.buf.length) {
      const nb = new Uint8Array(this.buf.length * 2);
      nb.set(this.buf.subarray(0, this.pos));
      this.buf = nb;
    }
  }
  writeBits(v, n) {
    if (n === 0) return;
    this.ensure();
    let bb = this.bitBuf | ((v & ((1 << n) - 1)) << this.bitCnt);
    let bc = this.bitCnt + n;
    while (bc >= 8) {
      this.buf[this.pos++] = bb & 0xff;
      bb >>>= 8;
      bc -= 8;
    }
    this.bitBuf = bb;
    this.bitCnt = bc;
  }
  // A Huffman code, stored bit-reversed so writeBits emits it MSB-first.
  writeCode(rev, len) {
    this.writeBits(rev, len);
  }
  flushToByte() {
    if (this.bitCnt > 0) {
      this.ensure();
      this.buf[this.pos++] = this.bitBuf & 0xff;
      this.bitBuf = 0;
      this.bitCnt = 0;
    }
  }
  toBytes() {
    return this.buf.subarray(0, this.pos);
  }
}

// ------------------------------------------------------------ Huffman codes

// Plain Huffman code lengths from frequencies (0 for unused symbols),
// built by repeatedly joining the two lightest nodes in a binary heap.
function buildTreeLengths(freqs) {
  const n = freqs.length;
  const lens = new Uint8Array(n);
  const syms = [];
  for (let i = 0; i < n; i++) if (freqs[i] > 0) syms.push(i);
  if (syms.length === 0) return lens;
  if (syms.length === 1) {
    lens[syms[0]] = 1;
    return lens;
  }
  const parent = new Int32Array(2 * n).fill(-1);
  const freq = new Float64Array(2 * n);
  for (let i = 0; i < n; i++) freq[i] = freqs[i];
  const heap = syms.slice();
  const less = (a, b) => freq[a] < freq[b] || (freq[a] === freq[b] && a < b);
  const siftDown = (h, i) => {
    for (;;) {
      const l = 2 * i + 1;
      const r = l + 1;
      let m = i;
      if (l < h.length && less(h[l], h[m])) m = l;
      if (r < h.length && less(h[r], h[m])) m = r;
      if (m === i) break;
      const t = h[i];
      h[i] = h[m];
      h[m] = t;
      i = m;
    }
  };
  for (let i = (heap.length >> 1) - 1; i >= 0; i--) siftDown(heap, i);
  const pop = () => {
    const top = heap[0];
    const last = heap.pop();
    if (heap.length > 0) {
      heap[0] = last;
      siftDown(heap, 0);
    }
    return top;
  };
  const push = (x) => {
    heap.push(x);
    let i = heap.length - 1;
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (!less(heap[i], heap[p])) break;
      const t = heap[i];
      heap[i] = heap[p];
      heap[p] = t;
      i = p;
    }
  };
  let next = n;
  while (heap.length > 1) {
    const a = pop();
    const b = pop();
    freq[next] = freq[a] + freq[b];
    parent[a] = next;
    parent[b] = next;
    push(next);
    next++;
  }
  for (const s of syms) {
    let d = 0;
    let x = s;
    while (parent[x] >= 0) {
      d++;
      x = parent[x];
    }
    lens[s] = d;
  }
  return lens;
}

// Length-limited Huffman lengths: rebuild with halved frequencies until no
// code exceeds maxLen (all-ones frequencies give a balanced tree, so this
// always terminates).
function buildLimitedLengths(freqs, maxLen) {
  let f = freqs;
  for (let a = 0; a < 24; a++) {
    const lens = buildTreeLengths(f);
    let mx = 0;
    for (let i = 0; i < lens.length; i++) if (lens[i] > mx) mx = lens[i];
    if (mx <= maxLen) return lens;
    const nf = new Uint32Array(f.length);
    for (let i = 0; i < f.length; i++) nf[i] = f[i] > 0 ? (f[i] + 1) >> 1 : 0;
    f = nf;
  }
  return buildTreeLengths(f);
}

// A deflate code needs at least two symbols with a length; give a dummy
// symbol length 1 when only one (or none) is used.
function padCodeLengths(lens) {
  let cnt = 0;
  let firstZero = -1;
  for (let i = 0; i < lens.length; i++) {
    if (lens[i] > 0) cnt++;
    else if (firstZero < 0) firstZero = i;
  }
  if (cnt === 0) {
    lens[0] = 1;
    if (lens.length > 1) lens[1] = 1;
  } else if (cnt === 1 && firstZero >= 0) lens[firstZero] = 1;
}

// Canonical codes from lengths; rev holds each code bit-reversed for writing.
function canonicalReversed(lengths) {
  let maxLen = 0;
  for (const l of lengths) if (l > maxLen) maxLen = l;
  const blCount = new Array(maxLen + 1).fill(0);
  for (const l of lengths) if (l > 0) blCount[l]++;
  const next = new Array(maxLen + 1).fill(0);
  let code = 0;
  for (let b = 1; b <= maxLen; b++) {
    code = (code + blCount[b - 1]) << 1;
    next[b] = code;
  }
  const rev = new Uint32Array(lengths.length);
  for (let s = 0; s < lengths.length; s++) {
    const l = lengths[s];
    if (l === 0) continue;
    const c = next[l]++;
    let r = 0;
    for (let k = 0; k < l; k++) r = (r << 1) | ((c >> k) & 1);
    rev[s] = r;
  }
  return rev;
}

// ------------------------------------------------------------ LZ77 matching

const HASH_BITS = 15;
const HASH_SIZE = 1 << HASH_BITS;
const HASH_MASK = HASH_SIZE - 1;

// Hash of the 3 bytes at data[i].
function hashTriple(d, i) {
  return ((d[i] << 10) ^ (d[i + 1] << 5) ^ d[i + 2]) & HASH_MASK;
}

// Link position pos into its hash chain.
function chainInsert(data, pos, head, prev) {
  const h = hashTriple(data, pos);
  prev[pos] = head[h];
  head[h] = pos;
}

// Longest match at pos down its chain (prevNode is pos's own chain entry);
// null when nothing reaches length 3.
function findLongestMatch(data, pos, end, prevNode, prev, chainLimit, niceLen) {
  const maxLen = Math.min(258, end - pos);
  if (maxLen < 3) return null;
  let bestLen = 0;
  let bestDist = 0;
  let cur = prevNode;
  let chain = chainLimit;
  while (cur >= 0 && chain-- > 0) {
    if (pos - cur > 32768) break;
    if (data[cur + bestLen] === data[pos + bestLen]) {
      let len = 0;
      while (len < maxLen && data[cur + len] === data[pos + len]) len++;
      if (len > bestLen) {
        bestLen = len;
        bestDist = pos - cur;
        if (len >= niceLen) break;
      }
    }
    cur = prev[cur];
  }
  return bestLen >= 3 ? { len: bestLen, dist: bestDist } : null;
}

// Lazy matching over data with a fixed-point bit-cost model (costs x1024).
// store: null to only count symbol frequencies into freqLit/freqDist, or a
// token store to fill. Returns the token count.
function parseTokens(data, litCost, lenCostSym, distCostSym, chainLimit, store, freqLit, freqDist) {
  const n = data.length;
  const head = new Int32Array(HASH_SIZE).fill(-1);
  const prev = new Int32Array(n).fill(-1);
  const matchCost = (len, dist) =>
    lenCostSym[LENGTH_SYMBOL[len] - 257] + LENGTH_EXTRA_BITS[len] * 1024 + distCostSym[DISTANCE_SYMBOL[dist]] + DISTANCE_EXTRA_BITS[dist] * 1024;
  let count = 0;
  let i = 0;
  if (n >= 3) chainInsert(data, 0, head, prev);
  while (i < n) {
    let m = null;
    if (i + 3 <= n) m = findLongestMatch(data, i, n, prev[i], prev, chainLimit, 258);
    if (m !== null) {
      let lc = 0;
      for (let k = 0; k < m.len; k++) lc += litCost[data[i + k]];
      if (matchCost(m.len, m.dist) < lc) {
        let m2 = null;
        if (i + 1 + 3 <= n) m2 = findLongestMatch(data, i + 1, n, head[hashTriple(data, i + 1)], prev, chainLimit, 258);
        if (m2 !== null && m2.len > m.len) {
          if (store) {
            store.isMatch[count] = 0;
            store.lit[count] = data[i];
            store.tpos[count] = i;
          }
          if (freqLit) freqLit[data[i]]++;
          count++;
          i++;
          if (i + 3 <= n) chainInsert(data, i, head, prev);
          continue;
        }
        if (store) {
          store.isMatch[count] = 1;
          store.mlen[count] = m.len;
          store.mdist[count] = m.dist;
          store.tpos[count] = i;
        }
        if (freqLit) {
          freqLit[LENGTH_SYMBOL[m.len]]++;
          freqDist[DISTANCE_SYMBOL[m.dist]]++;
        }
        count++;
        const ni = i + m.len;
        for (let j = i + 1; j < ni; j++) if (j + 3 <= n) chainInsert(data, j, head, prev);
        i = ni;
        if (i + 3 <= n) chainInsert(data, i, head, prev);
        continue;
      }
    }
    if (store) {
      store.isMatch[count] = 0;
      store.lit[count] = data[i];
      store.tpos[count] = i;
    }
    if (freqLit) freqLit[data[i]]++;
    count++;
    i++;
    if (i + 3 <= n) chainInsert(data, i, head, prev);
  }
  return count;
}

// ------------------------------------------------------------ block emit

const CL_ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];

// Run-length encode a code-length list for the dynamic header.
function runLengthEncodeLengths(lengths) {
  const items = [];
  const clFreq = new Uint32Array(19);
  let i = 0;
  const n = lengths.length;
  while (i < n) {
    const v = lengths[i];
    if (v === 0) {
      let run = 0;
      while (i + run < n && lengths[i + run] === 0) run++;
      i += run;
      while (run >= 11) {
        const take = Math.min(run, 138);
        items.push({ sym: 18, val: take - 11, bits: 7 });
        clFreq[18]++;
        run -= take;
      }
      if (run >= 3) {
        items.push({ sym: 17, val: run - 3, bits: 3 });
        clFreq[17]++;
        run = 0;
      }
      while (run > 0) {
        items.push({ sym: 0, val: 0, bits: 0 });
        clFreq[0]++;
        run--;
      }
    } else {
      items.push({ sym: v, val: 0, bits: 0 });
      clFreq[v]++;
      i++;
      let run = 0;
      while (i + run < n && lengths[i + run] === v) run++;
      i += run;
      while (run >= 3) {
        const take = Math.min(run, 6);
        items.push({ sym: 16, val: take - 3, bits: 2 });
        clFreq[16]++;
        run -= take;
      }
      while (run > 0) {
        items.push({ sym: v, val: 0, bits: 0 });
        clFreq[v]++;
        run--;
      }
    }
  }
  return { items, clFreq };
}

// One dynamic-Huffman deflate block holding tokens [from, to).
function writeDynamicBlock(bw, store, from, to, fL, fD, last) {
  const litLen = buildLimitedLengths(fL, 15);
  const distLen = buildLimitedLengths(fD, 15);
  padCodeLengths(litLen);
  padCodeLengths(distLen);
  let hlit = 257;
  for (let s = 285; s >= 257; s--) {
    if (litLen[s] > 0) {
      hlit = s + 1;
      break;
    }
  }
  let hdist = 1;
  for (let s = 29; s >= 0; s--) {
    if (distLen[s] > 0) {
      hdist = s + 1;
      break;
    }
  }
  const lengths = new Uint8Array(hlit + hdist);
  lengths.set(litLen.subarray(0, hlit), 0);
  lengths.set(distLen.subarray(0, hdist), hlit);
  const { items, clFreq } = runLengthEncodeLengths(lengths);
  const clLen = buildLimitedLengths(clFreq, 7);
  padCodeLengths(clLen);
  let hclen = 4;
  for (let k = 18; k >= 4; k--) {
    if (clLen[CL_ORDER[k]] > 0) {
      hclen = k + 1;
      break;
    }
  }
  const clRev = canonicalReversed(clLen);
  const litRev = canonicalReversed(litLen);
  const distRev = canonicalReversed(distLen);
  bw.writeBits(last ? 1 : 0, 1);
  bw.writeBits(2, 2);
  bw.writeBits(hlit - 257, 5);
  bw.writeBits(hdist - 1, 5);
  bw.writeBits(hclen - 4, 4);
  for (let k = 0; k < hclen; k++) bw.writeBits(clLen[CL_ORDER[k]], 3);
  for (const it of items) {
    bw.writeCode(clRev[it.sym], clLen[it.sym]);
    if (it.bits > 0) bw.writeBits(it.val, it.bits);
  }
  for (let t = from; t < to; t++) {
    if (store.isMatch[t]) {
      const len = store.mlen[t];
      const dist = store.mdist[t];
      const ls = LENGTH_SYMBOL[len];
      bw.writeCode(litRev[ls], litLen[ls]);
      if (LENGTH_EXTRA_BITS[len] > 0) bw.writeBits(len - LENGTH_BASE[ls - 257], LENGTH_EXTRA_BITS[len]);
      const ds = DISTANCE_SYMBOL[dist];
      bw.writeCode(distRev[ds], distLen[ds]);
      if (DISTANCE_EXTRA_BITS[dist] > 0) bw.writeBits(dist - DISTANCE_BASE[ds], DISTANCE_EXTRA_BITS[dist]);
    } else {
      const b = store.lit[t];
      bw.writeCode(litRev[b], litLen[b]);
    }
  }
  bw.writeCode(litRev[256], litLen[256]);
}

const DEFLATE_BLOCK_BYTES = 131072;
const FIRST_PASS_CHAIN = 64;

// Rough per-symbol bit costs (x1024) from raw byte frequencies, for the
// first lazy-matching pass: literals from self-information (clamped to
// 1..15 bits), lengths and distances from a fixed 8/6-bit guess plus extras.
function roughBitCosts(freqB, total) {
  const lit = new Int32Array(256);
  for (let b = 0; b < 256; b++) {
    const c = Math.round((-Math.log2((freqB[b] + 1) / (total + 256))) * 1024);
    lit[b] = c < 1024 ? 1024 : c > 15 * 1024 ? 15 * 1024 : c;
  }
  const len = new Int32Array(29);
  for (let s = 0; s < 29; s++) len[s] = (8 + LENGTH_EXTRA[s]) * 1024;
  const dist = new Int32Array(30);
  for (let s = 0; s < 30; s++) dist[s] = (6 + DISTANCE_EXTRA[s]) * 1024;
  return { lit, len, dist };
}

// Exact per-symbol bit costs (x1024) from a pass's Huffman lengths; an
// unused symbol costs 15 bits so the matcher still considers it.
function exactBitCosts(fLit, fDist) {
  const litLen = buildLimitedLengths(fLit, 15);
  const distLen = buildLimitedLengths(fDist, 15);
  const lit = new Int32Array(256);
  for (let b = 0; b < 256; b++) lit[b] = (litLen[b] || 15) * 1024;
  const len = new Int32Array(29);
  for (let s = 0; s < 29; s++) len[s] = (litLen[257 + s] || 15) * 1024;
  const dist = new Int32Array(30);
  for (let s = 0; s < 30; s++) dist[s] = (distLen[s] || 15) * 1024;
  return { lit, len, dist };
}

// A whole zlib stream of data from the hand-rolled deflate: two lazy
// matching passes (the first with rough costs, the second with the exact
// Huffman costs the first pass implies), split into fixed 128 KiB blocks.
// `chain2` is the second pass's hash-chain search limit.
function deflateCustom(data, chain2) {
  const freqB = new Uint32Array(256);
  for (let k = 0; k < data.length; k++) freqB[data[k]]++;
  const rough = roughBitCosts(freqB, data.length);
  const fLit = new Uint32Array(286);
  const fDist = new Uint32Array(30);
  parseTokens(data, rough.lit, rough.len, rough.dist, FIRST_PASS_CHAIN, null, fLit, fDist);
  const exact = exactBitCosts(fLit, fDist);
  const store = {
    isMatch: new Uint8Array(data.length),
    lit: new Uint8Array(data.length),
    mlen: new Uint16Array(data.length),
    mdist: new Uint16Array(data.length),
    tpos: new Uint32Array(data.length),
  };
  const count = parseTokens(data, exact.lit, exact.len, exact.dist, chain2, store, null, null);
  const bw = new BitWriter(data.length + 65536);
  bw.writeBits(0x78, 8);
  bw.writeBits(0x9c, 8);
  let bi = 0;
  let blockStart = 0;
  for (;;) {
    const blockEnd = Math.min(data.length, blockStart + DEFLATE_BLOCK_BYTES);
    let bj = bi;
    const fL = new Uint32Array(286);
    const fD = new Uint32Array(30);
    while (bj < count && store.tpos[bj] < blockEnd) {
      if (store.isMatch[bj]) {
        fL[LENGTH_SYMBOL[store.mlen[bj]]]++;
        fD[DISTANCE_SYMBOL[store.mdist[bj]]]++;
      } else fL[store.lit[bj]]++;
      bj++;
    }
    fL[256]++;
    const last = blockEnd >= data.length;
    writeDynamicBlock(bw, store, bi, bj, fL, fD, last);
    bi = bj;
    blockStart = blockEnd;
    if (last) break;
  }
  bw.flushToByte();
  const ad = adler32Of(data);
  bw.writeBits((ad >>> 24) & 255, 8);
  bw.writeBits((ad >>> 16) & 255, 8);
  bw.writeBits((ad >>> 8) & 255, 8);
  bw.writeBits(ad & 255, 8);
  return bw.toBytes();
}

// ---------------------------------------------------------------- PNG write

// Assemble a PNG file from [type, data] chunks, with CRCs.
function assemblePng(chunks) {
  let size = 8;
  for (const [, data] of chunks) size += 12 + data.length;
  const out = new Uint8Array(size);
  const view = new DataView(out.buffer);
  out.set(PNG_SIGNATURE, 0);
  let at = 8;
  for (const [type, data] of chunks) {
    view.setUint32(at, data.length);
    for (let k = 0; k < 4; k++) out[at + 4 + k] = type.charCodeAt(k);
    out.set(data, at + 8);
    view.setUint32(at + 8 + data.length, crc32Range(out, at + 4, at + 8 + data.length));
    at += 12 + data.length;
  }
  return out;
}

// The 13-byte IHDR chunk data for an 8-bit image of the given colour type.
function makeIhdr(width, height, colourType) {
  const d = new Uint8Array(13);
  const v = new DataView(d.buffer);
  v.setUint32(0, width);
  v.setUint32(4, height);
  d[8] = 8;
  d[9] = colourType;
  return d;
}

// Encode one form + one zlib stream as a complete PNG file.
function encodePng(width, height, form, idat) {
  const chunks = [['IHDR', makeIhdr(width, height, form.colourType)]];
  if (form.plte !== null) chunks.push(['PLTE', form.plte]);
  if (form.trns !== null) chunks.push(['tRNS', form.trns]);
  chunks.push(['IDAT', idat]);
  chunks.push(['IEND', new Uint8Array(0)]);
  return assemblePng(chunks);
}

// ---------------------------------------------------------------- screening

const SCREEN_OPTS = Object.freeze({ level: 6, memLevel: 8 });

// Screen every form/filter at zlib level 6 and keep each form's three
// smallest candidates (brute force is tried later, on the best form only).
function screenForms(forms, width, height) {
  const kept = [];
  for (const form of forms) {
    const chunks = auxChunkBytes(form);
    const cands = [];
    for (const choice of form.filters) {
      if (choice === 'brute') continue;
      const data = filterImage(form.samples, width, height, form.bpp, choice);
      const bytes = deflateSync(data, SCREEN_OPTS).length + chunks;
      cands.push({ form, choice, data, bytes });
    }
    cands.sort((a, b) => a.bytes - b.bytes);
    kept.push(cands.slice(0, 3));
  }
  return kept;
}

// From the screened candidates, pick the winner: try brute force on the
// best form, then compress every survivor with both deflates and keep the
// smallest complete file.
function chooseWinner(kept, width, height) {
  let bestIdx = 0;
  for (let k = 1; k < kept.length; k++) if (kept[k][0].bytes < kept[bestIdx][0].bytes) bestIdx = k;
  const bestForm = kept[bestIdx][0].form;
  if (bestForm.filters.includes('brute')) {
    const data = filterImage(bestForm.samples, width, height, bestForm.bpp, 'brute');
    const bytes = deflateSync(data, SCREEN_OPTS).length + auxChunkBytes(bestForm);
    const list = kept[bestIdx];
    if (bytes < list[list.length - 1].bytes) {
      list.push({ form: bestForm, choice: 'brute', data, bytes });
      list.sort((a, b) => a.bytes - b.bytes);
    }
  }
  let winner = null;
  for (const list of kept) {
    for (const cand of list) {
      // Unfiltered rows carry long-range repeats: search them far. Filtered
      // rows gain nothing from very long chains, so search them less.
      const own = deflateCustom(cand.data, cand.choice === 0 ? 1024 : 256);
      const z9 = deflateSync(cand.data, { level: 9, memLevel: 9 });
      const stream = own.length <= z9.length ? own : z9;
      const total = stream.length + auxChunkBytes(cand.form);
      if (winner === null || total < winner.total) winner = { form: cand.form, stream, total };
    }
  }
  return encodePng(width, height, winner.form, winner.stream);
}

// Compress one image: screen its forms, then pick the winner.
function compressImage(rgba, width, height) {
  return chooseWinner(screenForms(candidateForms(rgba), width, height), width, height);
}

// ---------------------------------------------------------------- main

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

for (const id of readdirSync(INPUT_DIR).sort()) {
  if (!statSync(join(INPUT_DIR, id)).isDirectory()) continue;
  const image = readPngToRgba(new Uint8Array(readFileSync(join(INPUT_DIR, id, 'image.png'))));
  const out = compressImage(image.rgba, image.width, image.height);
  mkdirSync(join(OUTPUT_DIR, id), { recursive: true });
  const outPath = join(OUTPUT_DIR, id, 'image.png');
  writeFileSync(outPath, out, { mode: 0o644 });
  chmodSync(outPath, 0o644); // mode above is masked by umask; force 0644
  console.log(id + ' ' + out.length + ' bytes');
}
