// ============================================================================
//  WA BOT - Baileys (@whiskeysockets/baileys)
//
//  Instal   : npm install @whiskeysockets/baileys @hapi/boom sharp pino qrcode
//  Jalankan : node index.js        (butuh Node.js 18 ke atas)
//  Opsional : taruh gambar logo.png di folder yang sama untuk menu bergambar
//
//  Catatan  : file ini sengaja ASCII-only. Semua emoji dan karakter kotak
//             ditulis dengan kode \u{...} supaya aman dibuka di Notepad Windows.
// ============================================================================
import makeWASocket, {
    useMultiFileAuthState,
    DisconnectReason,
    downloadMediaMessage,
    fetchLatestBaileysVersion
} from '@whiskeysockets/baileys';
import { Boom } from '@hapi/boom';
import sharp from 'sharp';
import pino from 'pino';
import QRCode from 'qrcode';
import readline from 'readline';
import crypto from 'crypto';
import fs from 'fs';
import { spawn } from 'child_process';

// ----------------------------------------------------------------------------
// KONFIGURASI
// ----------------------------------------------------------------------------
const PREFIX = '!';
const FOLDER_SESI = 'sesi_bot';
const FILE_CATATAN = 'catatan.json';
const FILE_LOGO = 'logo.png';
const FILE_PENGINGAT = 'pengingat.json';
const MAKS_CATATAN = 100;          // maksimal catatan per nomor
const MAKS_PANJANG_CATATAN = 500;  // maksimal karakter per catatan
const MAKS_ANTREAN = 50;           // maksimal chat di antrean terminal
const COOLDOWN_MS = 1500;          // jeda antar perintah per pengirim
const MAKS_PENGINGAT = 20;         // maksimal pengingat aktif per nomor
const MAKS_HARI_PENGINGAT = 30;    // pengingat paling jauh 30 hari
const UA = 'Mozilla/5.0 (compatible; WaBot/1.0; personal use)';

const logger = pino({ level: 'silent' });
const WAKTU_MULAI = Date.now();

// ----------------------------------------------------------------------------
// EMOJI & KARAKTER KOTAK (semua pakai kode Unicode)
// ----------------------------------------------------------------------------
const E = {
    robot: '\u{1F916}', art: '\u{1F3A8}', memo: '\u{1F4DD}', list: '\u{1F4CB}',
    trash: '\u{1F5D1}\u{FE0F}', tools: '\u{1F6E0}\u{FE0F}', dice: '\u{1F3B2}',
    pic: '\u{1F5BC}\u{FE0F}', qr: '\u{1F533}', mic: '\u{1F3A4}', calc: '\u{1F9EE}',
    sun: '\u{26C5}', money: '\u{1F4B1}', link: '\u{1F517}', book: '\u{1F4D6}',
    spark: '\u{2728}', bulb: '\u{1F4A1}', clock: '\u{23F0}', ping: '\u{1F3D3}',
    check: '\u{2705}', cross: '\u{274C}', warn: '\u{26A0}\u{FE0F}', temp: '\u{1F321}\u{FE0F}',
    drop: '\u{1F4A7}', wind: '\u{1F4A8}', globe: '\u{1F30D}', clover: '\u{1F340}',
    inbox: '\u{1F4ED}', chart: '\u{1F4CA}', up: '\u{23F1}\u{FE0F}', search: '\u{1F50D}',
    heart: '\u{2764}\u{FE0F}', cupid: '\u{1F498}', bell: '\u{1F514}', mosque: '\u{1F54C}',
    crystal: '\u{1F52E}', handshake: '\u{1F91D}', speech: '\u{1F4AC}', hearts: '\u{1F495}'
};

const B = {
    TL: '\u{256D}', BL: '\u{2570}', V: '\u{2502}', H: '\u{2500}', R: '\u{203A}',
    FULL: '\u{2588}', EMPTY: '\u{2591}'
};
const GARIS = B.H.repeat(14);

// ----------------------------------------------------------------------------
// STATE GLOBAL
// ----------------------------------------------------------------------------
const rl = readline.createInterface({ input: process.stdin, output: process.stdout });
const tanya = (q) => new Promise((res) => rl.question(q, res));

let sock = null;
let terminalAktif = false;
let pairingBerjalan = false;
let terhubung = false;              // status koneksi WhatsApp saat ini
let pengingatAktif = false;         // penjadwal pengingat sudah berjalan
let cekBerjalan = false;            // mencegah cekPengingat tumpang tindih
const sentIds = new Set();          // id pesan yang dikirim bot (supaya tidak diproses ulang)
const antreanChat = [];             // chat pribadi non-perintah untuk dibalas manual
const cooldown = new Map();         // idPengirim -> waktu perintah terakhir

// ----------------------------------------------------------------------------
// HELPER UMUM
// ----------------------------------------------------------------------------
const pilihAcak = (arr) => arr[Math.floor(Math.random() * arr.length)];

async function ambilResponse(url, tipe) {
    const r = await fetch(url, {
        signal: AbortSignal.timeout(12000),
        headers: { 'User-Agent': UA, Accept: '*/*' }
    });
    if (!r.ok) throw new Error(`HTTP ${r.status}`);
    return tipe === 'json' ? r.json() : tipe === 'buffer' ? Buffer.from(await r.arrayBuffer()) : r.text();
}
const getJSON = (url) => ambilResponse(url, 'json');

function formatDurasi(ms, tanpaDetik = false) {
    const d = Math.floor(ms / 1000);
    const hari = Math.floor(d / 86400);
    const jam = Math.floor((d % 86400) / 3600);
    const menit = Math.floor((d % 3600) / 60);
    const detik = d % 60;
    return [hari && `${hari} hari`, jam && `${jam} jam`, menit && `${menit} menit`, (!tanpaDetik || ms < 60000) && `${detik} detik`]
        .filter(Boolean).join(' ');
}

function sekarangWIB() {
    return new Date().toLocaleString('id-ID', {
        timeZone: 'Asia/Jakarta', dateStyle: 'full', timeStyle: 'medium'
    }).replace('pukul', '|') + ' WIB';
}

function parseAngka(s) {
    let t = s.replace(/\s/g, '').replace(/^rp\.?/i, '').replace(/^\$/, '');
    if (!/^[0-9.,]+$/.test(t)) return NaN;
    if (t.includes('.') && t.includes(',')) {
        t = t.replace(/\./g, '').replace(',', '.');          // 1.000,50
    } else if (t.includes(',')) {
        t = (t.match(/,/g).length > 1) ? t.replace(/,/g, '') : t.replace(',', '.');
    } else if (/^\d{1,3}(\.\d{3})+$/.test(t)) {
        t = t.replace(/\./g, '');                            // 1.000.000
    }
    return parseFloat(t);
}

function potongTeks(teks, maks = 180) {
    const hasil = [];
    let cur = '';
    for (const kata of teks.split(/\s+/)) {
        if ((cur + ' ' + kata).trim().length > maks) {
            if (cur) hasil.push(cur);
            cur = kata.slice(0, maks);
        } else {
            cur = (cur + ' ' + kata).trim();
        }
    }
    if (cur) hasil.push(cur);
    return hasil;
}

// ----------------------------------------------------------------------------
// PENYIMPANAN CATATAN (JSON, dipisah per nomor)
// Format: { "628123456789": ["catatan 1", "catatan 2"] }
// ----------------------------------------------------------------------------
function siapkanFileCatatan() {
    if (fs.existsSync(FILE_CATATAN)) {
        try {
            const d = JSON.parse(fs.readFileSync(FILE_CATATAN, 'utf-8'));
            if (Array.isArray(d)) {
                // Format lama (satu daftar untuk semua orang): diamankan, bukan dihapus
                fs.renameSync(FILE_CATATAN, 'catatan_lama.json');
                console.log('Format catatan lama terdeteksi, disimpan sebagai catatan_lama.json');
            } else {
                return;
            }
        } catch {
            fs.renameSync(FILE_CATATAN, `catatan_rusak_${Date.now()}.json`);
        }
    }
    fs.writeFileSync(FILE_CATATAN, '{}');
}

function bacaCatatan() {
    try {
        const d = JSON.parse(fs.readFileSync(FILE_CATATAN, 'utf-8'));
        return d && typeof d === 'object' && !Array.isArray(d) ? d : {};
    } catch {
        return {};
    }
}

function simpanCatatan(data) {
    const tmp = FILE_CATATAN + '.tmp';
    fs.writeFileSync(tmp, JSON.stringify(data, null, 2));
    fs.renameSync(tmp, FILE_CATATAN);   // tulis atomik supaya file tidak rusak
}

// ----------------------------------------------------------------------------
// KALKULATOR AMAN (tanpa eval)
// Dukung: + - * / % ^ ( ) desimal, juga x untuk kali dan : untuk bagi
// ----------------------------------------------------------------------------
function hitung(ekspresi) {
    const s = ekspresi.toLowerCase()
        .replace(/,/g, '.')
        .replace(/[x\u00D7]/g, '*')
        .replace(/[:\u00F7]/g, '/')
        .replace(/\s+/g, '');
    if (!s || s.length > 100 || !/^[0-9+\-*/%^().]+$/.test(s)) throw new Error('Rumus tidak valid');

    let i = 0;
    let kedalaman = 0;

    function primary() {
        if (s[i] === '(') {
            if (++kedalaman > 30) throw new Error('Kurung terlalu dalam');
            i++;
            const v = expr();
            if (s[i] !== ')') throw new Error('Kurung tidak seimbang');
            i++;
            kedalaman--;
            return v;
        }
        const m = /^(\d+\.?\d*|\.\d+)/.exec(s.slice(i));
        if (!m) throw new Error('Rumus tidak valid');
        i += m[0].length;
        return parseFloat(m[0]);
    }
    function pangkat() {
        const dasar = primary();
        if (s[i] === '^') { i++; return Math.pow(dasar, unary()); }
        return dasar;
    }
    function unary() {
        if (s[i] === '-') { i++; return -unary(); }
        if (s[i] === '+') { i++; return unary(); }
        return pangkat();
    }
    function term() {
        let v = unary();
        while (s[i] === '*' || s[i] === '/' || s[i] === '%') {
            const op = s[i++];
            const r = unary();
            v = op === '*' ? v * r : op === '/' ? v / r : v % r;
        }
        return v;
    }
    function expr() {
        let v = term();
        while (s[i] === '+' || s[i] === '-') {
            const op = s[i++];
            const r = term();
            v = op === '+' ? v + r : v - r;
        }
        return v;
    }

    const hasil = expr();
    if (i < s.length) throw new Error('Rumus tidak valid');
    if (!Number.isFinite(hasil)) throw new Error('Hasil tidak terdefinisi (misal bagi nol)');
    return hasil;
}

// ----------------------------------------------------------------------------
// LAYANAN EKSTERNAL (gratis, tanpa API key)
// ----------------------------------------------------------------------------
const KODE_CUACA = {
    0: 'Cerah', 1: 'Cerah berawan', 2: 'Berawan sebagian', 3: 'Mendung',
    45: 'Berkabut', 48: 'Kabut beku', 51: 'Gerimis ringan', 53: 'Gerimis', 55: 'Gerimis lebat',
    56: 'Gerimis beku', 57: 'Gerimis beku lebat', 61: 'Hujan ringan', 63: 'Hujan sedang',
    65: 'Hujan lebat', 66: 'Hujan beku', 67: 'Hujan beku lebat', 71: 'Salju ringan',
    73: 'Salju', 75: 'Salju lebat', 77: 'Butiran salju', 80: 'Hujan shower ringan',
    81: 'Hujan shower', 82: 'Hujan shower deras', 85: 'Salju shower', 86: 'Salju shower lebat',
    95: 'Badai petir', 96: 'Badai petir dan hujan es', 99: 'Badai petir dan hujan es lebat'
};

async function ambilCuaca(kota) {
    const geo = await getJSON(
        `https://geocoding-api.open-meteo.com/v1/search?name=${encodeURIComponent(kota)}&count=1&language=id&format=json`
    );
    const lokasi = geo?.results?.[0];
    if (!lokasi) return null;
    const cuaca = await getJSON(
        `https://api.open-meteo.com/v1/forecast?latitude=${lokasi.latitude}&longitude=${lokasi.longitude}` +
        '&current=temperature_2m,relative_humidity_2m,apparent_temperature,weather_code,wind_speed_10m&timezone=auto'
    );
    return { lokasi, now: cuaca.current };
}

async function ambilKurs() {
    try {
        const d = await getJSON('https://open.er-api.com/v6/latest/USD');
        if (d?.rates?.IDR) {
            return { rate: d.rates.IDR, waktu: (d.time_last_update_utc || '').replace(/ \+0000$/, ' UTC') };
        }
    } catch { /* lanjut ke sumber cadangan */ }
    const d = await getJSON('https://api.frankfurter.dev/v1/latest?base=USD&symbols=IDR');
    if (d?.rates?.IDR) return { rate: d.rates.IDR, waktu: d.date };
    throw new Error('Kurs tidak tersedia');
}

async function cariWiki(kata) {
    const cari = await getJSON(
        `https://id.wikipedia.org/w/api.php?action=opensearch&search=${encodeURIComponent(kata)}&limit=1&namespace=0&format=json`
    );
    const judul = cari?.[1]?.[0];
    if (!judul) return null;
    return getJSON(
        `https://id.wikipedia.org/api/rest_v1/page/summary/${encodeURIComponent(judul.replace(/ /g, '_'))}`
    );
}

async function buatSuara(teks) {
    const bagian = potongTeks(teks);
    const buffers = [];
    for (const b of bagian) {
        buffers.push(await ambilResponse(
            `https://translate.google.com/translate_tts?ie=UTF-8&client=tw-ob&tl=id&q=${encodeURIComponent(b)}`,
            'buffer'
        ));
    }
    return Buffer.concat(buffers);
}

// ----------------------------------------------------------------------------
// DATA HIBURAN
// ----------------------------------------------------------------------------
const QUOTES = [
    'Mulai saja dulu, sempurnakan sambil jalan.',
    'Konsisten kecil setiap hari mengalahkan semangat besar sesekali.',
    'Gagal itu biasa, berhenti itu pilihan.',
    'Jangan bandingkan bab satu hidupmu dengan bab sepuluh hidup orang lain.',
    'Apa yang kamu lakukan hari ini adalah hadiah untuk dirimu di masa depan.',
    'Sabar bukan berarti diam, tapi tetap berusaha sambil percaya pada waktu.',
    'Mimpi tanpa tindakan hanya akan jadi cerita sebelum tidur.',
    'Langkah kecil hari ini tetap lebih jauh dari rencana besar yang tak pernah dimulai.',
    'Istirahat boleh, menyerah jangan.',
    'Orang kuat bukan yang tak pernah jatuh, tapi yang selalu bangun lagi.',
    'Fokus pada progres, bukan kesempurnaan.',
    'Kesempatan lebih sering datang pada mereka yang terus bergerak.'
];

const FAKTA = [
    'Gurita punya tiga jantung dan darahnya berwarna biru.',
    'Di planet Venus, satu hari (satu rotasi) lebih lama daripada satu tahunnya.',
    'Secara botani, pisang termasuk buah beri, sedangkan stroberi bukan.',
    'Jantung udang terletak di bagian kepalanya.',
    'Wombat adalah satu-satunya hewan yang kotorannya berbentuk kubus.',
    'Otak manusia hanya sekitar 2% dari berat tubuh, tapi memakai sekitar 20% energi tubuh.',
    'Kupu-kupu bisa merasakan rasa lewat kakinya.',
    'Cahaya matahari butuh sekitar 8 menit 20 detik untuk sampai ke Bumi.',
    'Lumba-lumba memiliki siulan khas yang berfungsi seperti nama panggilan.',
    'Hiu sudah ada di Bumi lebih lama daripada pohon.',
    'Candi Borobudur di Magelang adalah candi Buddha terbesar di dunia.',
    'Menara Eiffel bisa memuai hingga belasan sentimeter saat cuaca panas.',
    'Indonesia memiliki sekitar 17.000 pulau, menjadikannya negara kepulauan terbesar di dunia.',
    'Madu yang disimpan baik hampir tidak pernah basi.',
    'Sidik lidah setiap orang unik, seperti sidik jari.'
];

// ----------------------------------------------------------------------------
// JODOH & ZODIAK (hiburan; hasil tetap dan simetris)
// ----------------------------------------------------------------------------
const bersihkanNama = (n) => n.replace(/[*_~`]/g, '').replace(/\s+/g, ' ').trim();
const batas = (v) => Math.max(0, Math.min(100, v));

function bar10(persen) {
    const penuh = Math.round(persen / 10);
    return B.FULL.repeat(penuh) + B.EMPTY.repeat(10 - penuh);
}

// Urutan nama tidak berpengaruh: "Budi & Ani" sama dengan "Ani & Budi"
function hitungJodoh(a, b) {
    const [x, y] = [a, b].map((n) => bersihkanNama(n).toLowerCase()).sort();
    if (x === y) return { persen: 100, cinta: 100, komunikasi: 100, kesetiaan: 100, sama: true };
    const h = crypto.createHash('sha256').update(`${x}|${y}`).digest();
    const persen = h.readUInt16BE(0) % 101;
    const variasi = (i) => batas(persen + (h[2 + i] % 31) - 15);
    return { persen, cinta: variasi(0), komunikasi: variasi(1), kesetiaan: variasi(2), sama: false };
}

function komentarJodoh(persen, sama) {
    if (sama) return 'Mencintai diri sendiri itu penting!';
    if (persen >= 90) return 'Jodoh sejati! Tinggal tentukan tanggalnya.';
    if (persen >= 75) return 'Cocok banget, jangan disia-siakan.';
    if (persen >= 60) return 'Cukup serasi, tinggal saling mengerti.';
    if (persen >= 40) return 'Masih bisa diperjuangkan, butuh usaha ekstra.';
    if (persen >= 20) return 'Hmm, mungkin lebih cocok jadi teman.';
    return 'Maaf ya, mending jadi kenangan.';
}

const HARI_BULAN = [31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
const BATAS_ZODIAK = [
    [1, 20, 'Aquarius'], [2, 19, 'Pisces'], [3, 21, 'Aries'], [4, 20, 'Taurus'],
    [5, 21, 'Gemini'], [6, 21, 'Cancer'], [7, 23, 'Leo'], [8, 23, 'Virgo'],
    [9, 23, 'Libra'], [10, 23, 'Scorpio'], [11, 22, 'Sagittarius'], [12, 22, 'Capricorn']
];
const TANDA = {
    Aries: ['\u{2648}\u{FE0F}', 'Api'], Taurus: ['\u{2649}\u{FE0F}', 'Tanah'],
    Gemini: ['\u{264A}\u{FE0F}', 'Udara'], Cancer: ['\u{264B}\u{FE0F}', 'Air'],
    Leo: ['\u{264C}\u{FE0F}', 'Api'], Virgo: ['\u{264D}\u{FE0F}', 'Tanah'],
    Libra: ['\u{264E}\u{FE0F}', 'Udara'], Scorpio: ['\u{264F}\u{FE0F}', 'Air'],
    Sagittarius: ['\u{2650}\u{FE0F}', 'Api'], Capricorn: ['\u{2651}\u{FE0F}', 'Tanah'],
    Aquarius: ['\u{2652}\u{FE0F}', 'Udara'], Pisces: ['\u{2653}\u{FE0F}', 'Air']
};
const UNSUR_COCOK = {
    'Api|Api': 85, 'Tanah|Tanah': 85, 'Udara|Udara': 85, 'Air|Air': 85,
    'Api|Udara': 80, 'Air|Tanah': 80, 'Api|Tanah': 55, 'Air|Udara': 55,
    'Air|Api': 40, 'Tanah|Udara': 40
};

function cariZodiak(hari, bulan) {
    const [, mulai, nama] = BATAS_ZODIAK[bulan - 1];
    return hari >= mulai ? nama : BATAS_ZODIAK[(bulan + 10) % 12][2];
}

// Terima "14-2 20-8", "14/02/2000 20/08/1999", atau "14 2 20 8"
function parseDuaTanggal(args) {
    const token = args.trim().split(/\s+/);
    let pasang = null;
    if (token.length === 2) {
        pasang = token.map((t) => (t.match(/\d+/g) || []).map(Number));
    } else {
        const n = (args.match(/\d+/g) || []).map(Number);
        if (n.length === 4) pasang = [[n[0], n[1]], [n[2], n[3]]];
    }
    if (!pasang || pasang.some((p) => p.length < 2)) return null;
    const hasil = pasang.map(([hari, bulan]) => ({ hari, bulan }));
    const valid = hasil.every(({ hari, bulan }) =>
        bulan >= 1 && bulan <= 12 && hari >= 1 && hari <= HARI_BULAN[bulan - 1]);
    return valid ? hasil : null;
}

function hitungZodiak(z1, z2) {
    const kunci = [TANDA[z1][1], TANDA[z2][1]].sort().join('|');
    const h = crypto.createHash('sha256').update([z1, z2].sort().join('|')).digest();
    return batas(UNSUR_COCOK[kunci] + (h[0] % 11) - 5);
}

// ----------------------------------------------------------------------------
// PENGINGAT (disimpan di JSON, tetap ada walau bot dimatikan)
// ----------------------------------------------------------------------------
const SATUAN_MS = { hari: 86400000, jam: 3600000, j: 3600000, h: 3600000, menit: 60000, m: 60000 };

// "1j30m beli kopi" -> { ms: 5400000, pesan: 'beli kopi' }
function parseWaktuPengingat(args) {
    const m = /^((?:\d+\s*(?:hari|jam|menit|j|h|m)(?![a-z])\s*)+)(.+)$/is.exec(args);
    if (!m) return null;
    let ms = 0;
    for (const [, n, u] of m[1].matchAll(/(\d+)\s*(hari|jam|menit|j|h|m)/gi)) {
        ms += parseInt(n, 10) * SATUAN_MS[u.toLowerCase()];
    }
    return { ms, pesan: m[2].trim() };
}

const formatWaktuWIB = (ms) => new Date(ms).toLocaleString('id-ID', {
    timeZone: 'Asia/Jakarta', dateStyle: 'medium', timeStyle: 'short'
}) + ' WIB';

function siapkanFilePengingat() {
    if (!fs.existsSync(FILE_PENGINGAT)) fs.writeFileSync(FILE_PENGINGAT, '[]');
}

function bacaPengingat() {
    try {
        const d = JSON.parse(fs.readFileSync(FILE_PENGINGAT, 'utf-8'));
        return Array.isArray(d) ? d : [];
    } catch {
        return [];
    }
}

function simpanPengingat(data) {
    const tmp = FILE_PENGINGAT + '.tmp';
    fs.writeFileSync(tmp, JSON.stringify(data, null, 2));
    fs.renameSync(tmp, FILE_PENGINGAT);
}

// Dipanggil tiap 15 detik: kirim pengingat yang sudah jatuh tempo
async function cekPengingat() {
    if (cekBerjalan || !terhubung || !sock) return;
    cekBerjalan = true;
    try {
        const sekarang = Date.now();
        const jatuhTempo = bacaPengingat().filter((p) => p.waktu <= sekarang);
        if (!jatuhTempo.length) return;

        const selesai = new Set();
        const gagalMap = new Map();
        for (const p of jatuhTempo) {
            try {
                const telat = sekarang - p.waktu > 120000;
                await kirim(p.jid, {
                    text: `${E.bell} *PENGINGAT*\n${p.pesan}` +
                        (telat ? '\n\n_(terlambat karena bot sempat mati/terputus)_' : '')
                });
                selesai.add(p.id);
            } catch (e) {
                const gagal = (p.gagal || 0) + 1;
                console.log(`[PENGINGAT] gagal kirim (${gagal}/5):`, e.message);
                if (gagal >= 5) selesai.add(p.id); else gagalMap.set(p.id, gagal);
            }
        }
        // Baca ulang file supaya pengingat yang baru dibuat selama pengiriman tidak hilang
        simpanPengingat(
            bacaPengingat()
                .filter((p) => !selesai.has(p.id))
                .map((p) => (gagalMap.has(p.id) ? { ...p, gagal: gagalMap.get(p.id) } : p))
        );
    } finally {
        cekBerjalan = false;
    }
}

function jalankanPengingat() {
    if (pengingatAktif) return;
    pengingatAktif = true;
    setInterval(cekPengingat, 15000);
    cekPengingat();
}

// ----------------------------------------------------------------------------
// JADWAL SHOLAT (Aladhan; metode Kemenag RI untuk lokasi di Indonesia)
// ----------------------------------------------------------------------------
const WAKTU_SHOLAT = [['Fajr', 'Subuh'], ['Dhuhr', 'Dzuhur'], ['Asr', 'Ashar'], ['Maghrib', 'Maghrib'], ['Isha', 'Isya']];
const LABEL_ZONA = { 'Asia/Jakarta': 'WIB', 'Asia/Pontianak': 'WIB', 'Asia/Makassar': 'WITA', 'Asia/Jayapura': 'WIT' };

async function ambilJadwalSholat(kota) {
    const geo = await getJSON(
        `https://geocoding-api.open-meteo.com/v1/search?name=${encodeURIComponent(kota)}&count=1&language=id&format=json`
    );
    const l = geo?.results?.[0];
    if (!l) return null;

    const tz = l.timezone || 'Asia/Jakarta';
    const tanggal = new Date().toLocaleDateString('en-GB', { timeZone: tz }).replace(/\//g, '-');  // DD-MM-YYYY
    const metode = l.country_code === 'ID' ? '&method=20' : '';
    const d = await getJSON(
        `https://api.aladhan.com/v1/timings/${tanggal}?latitude=${l.latitude}&longitude=${l.longitude}` +
        `&timezonestring=${encodeURIComponent(tz)}${metode}`
    );
    const t = d?.data?.timings;
    if (!t) throw new Error('Jadwal tidak tersedia');

    const jam = (v) => ((/\d{1,2}:\d{2}/.exec(v) || [''])[0]).padStart(5, '0');
    const sekarang = new Date().toLocaleTimeString('en-GB', {
        timeZone: tz, hour: '2-digit', minute: '2-digit', hourCycle: 'h23'
    });
    const lima = WAKTU_SHOLAT.map(([kunci, nama]) => ({ nama, jam: jam(t[kunci]) }));
    const berikut = lima.find((x) => x.jam > sekarang)?.nama || 'Subuh';

    return {
        lokasi: l,
        zona: LABEL_ZONA[tz] || tz,
        tanggal: new Date().toLocaleDateString('id-ID', { timeZone: tz, dateStyle: 'full' }),
        terbit: jam(t.Sunrise),
        lima,
        berikut,
        kemenag: !!metode
    };
}

// ----------------------------------------------------------------------------
// KONVERSI SUARA: MP3 -> OGG/Opus (format voice note asli WhatsApp)
// Pakai ffmpeg-static (npm install ffmpeg-static) atau ffmpeg di PATH
// ----------------------------------------------------------------------------
async function keOpus(mp3) {
    let ffmpeg = 'ffmpeg';
    try {
        const mod = await import('ffmpeg-static');
        if (mod.default) ffmpeg = mod.default;
    } catch { /* pakai ffmpeg dari PATH */ }

    return new Promise((resolve, reject) => {
        const p = spawn(ffmpeg, [
            '-loglevel', 'error', '-i', 'pipe:0', '-vn',
            '-c:a', 'libopus', '-b:a', '32k', '-ar', '48000', '-ac', '1', '-f', 'ogg', 'pipe:1'
        ]);
        const out = [];
        const err = [];
        p.stdout.on('data', (d) => out.push(d));
        p.stderr.on('data', (d) => err.push(d));
        p.stdin.on('error', () => {});
        p.on('error', reject);
        p.on('close', (code) => {
            if (code === 0 && out.length) resolve(Buffer.concat(out));
            else reject(new Error('ffmpeg gagal: ' + Buffer.concat(err).toString().slice(0, 200)));
        });
        p.stdin.end(mp3);
    });
}

// ----------------------------------------------------------------------------
// MENU
// ----------------------------------------------------------------------------
const kotak = (judul, baris) => [
    `${B.TL}${B.H} ${judul}`,
    ...baris.map((b) => `${B.V} ${b}`),
    `${B.BL}${GARIS}`
].join('\n');

function buatMenu(nama) {
    const r = B.R;
    return [
        `${B.TL}${GARIS}`,
        `${B.V} ${E.robot} *WA BOT*`,
        `${B.V} Halo, ${nama}!`,
        `${B.V} Awali perintah dengan *${PREFIX}*`,
        `${B.BL}${GARIS}`,
        '',
        kotak(`${E.art} *MEDIA & KREATIF*`, [
            `${r} *!stiker* / *!s*  _foto jadi stiker_`,
            `${r} *!toimg*  _reply stiker jadi gambar_`,
            `${r} *!qr* [teks/link]  _buat QR Code_`,
            `${r} *!tts* [teks]  _teks jadi suara_`
        ]),
        '',
        kotak(`${E.memo} *CATATAN PRIBADI*`, [
            `${r} *!catat* [teks]  _simpan catatan_`,
            `${r} *!catatan*  _lihat catatanmu_`,
            `${r} *!hapus* [nomor]  _hapus satu catatan_`,
            `${r} *!hapuscatatan*  _hapus semua_`
        ]),
        '',
        kotak(`${E.tools} *ALAT & PENCARIAN*`, [
            `${r} *!hitung* [rumus]  _kalkulator_`,
            `${r} *!cuaca* [kota]  _cuaca terkini_`,
            `${r} *!kurs* [jumlah]  _USD ke IDR_`,
            `${r} *!singkat* [url]  _pendekkan link_`,
            `${r} *!wiki* [kata]  _cari di Wikipedia_`,
            `${r} *!sholat* [kota]  _jadwal sholat hari ini_`
        ]),
        '',
        kotak(`${E.bell} *PENGINGAT*`, [
            `${r} *!ingatkan* [waktu] [pesan]  _contoh: 30m minum obat_`,
            `${r} *!pengingat*  _lihat pengingat aktif_`,
            `${r} *!batalingat* [nomor]  _batalkan_`
        ]),
        '',
        kotak(`${E.dice} *HIBURAN & STATUS*`, [
            `${r} *!quotes*  _kutipan motivasi_`,
            `${r} *!fakta*  _fakta unik_`,
            `${r} *!gacha*  _hoki harianmu_`,
            `${r} *!jodoh* [nama] & [nama]  _cek kecocokan_`,
            `${r} *!zodiak* [tgl-bln] [tgl-bln]  _cocok zodiak_`,
            `${r} *!status* / *!ping*  _info bot_`
        ])
    ].join('\n');
}

// ----------------------------------------------------------------------------
// HELPER PESAN
// ----------------------------------------------------------------------------
const PEMBUNGKUS = [
    'ephemeralMessage', 'viewOnceMessage', 'viewOnceMessageV2',
    'viewOnceMessageV2Extension', 'documentWithCaptionMessage'
];

function bukaPesan(m) {
    let x = m;
    while (x) {
        const k = PEMBUNGKUS.find((p) => x[p]);
        if (!k) break;
        x = x[k].message;
    }
    return x;
}

const ambilTeks = (m) => (
    m?.conversation ||
    m?.extendedTextMessage?.text ||
    m?.imageMessage?.caption ||
    m?.videoMessage?.caption ||
    ''
).trim();

function jenisMedia(m) {
    if (m?.imageMessage) return '[Foto]';
    if (m?.videoMessage) return '[Video]';
    if (m?.audioMessage) return '[Suara]';
    if (m?.stickerMessage) return '[Stiker]';
    if (m?.documentMessage) return '[Dokumen]';
    if (m?.contactMessage) return '[Kontak]';
    if (m?.locationMessage) return '[Lokasi]';
    return '[Pesan]';
}

function ambilQuoted(msg, isi) {
    const ctx = isi?.extendedTextMessage?.contextInfo || isi?.imageMessage?.contextInfo;
    if (!ctx?.quotedMessage) return null;
    return {
        key: { remoteJid: msg.key.remoteJid, id: ctx.stanzaId, participant: ctx.participant },
        message: bukaPesan(ctx.quotedMessage)
    };
}

// Cari media bertipe tertentu: dari pesan itu sendiri, atau dari pesan yang di-reply
function ambilMedia(msg, isi, jenis) {
    if (isi?.[jenis]) return { key: msg.key, message: isi };
    const q = ambilQuoted(msg, isi);
    return q?.message?.[jenis] ? q : null;
}

const unduh = (target) => downloadMediaMessage(
    target, 'buffer', {}, { logger, reuploadRequest: sock.updateMediaMessage }
);

const kirim = async (to, content, opt = {}) => {
    const res = await sock.sendMessage(to, content, opt);
    if (res?.key?.id) {
        if (sentIds.size > 500) sentIds.clear();
        sentIds.add(res.key.id);
    }
    return res;
};
const balas = (c, teks) => kirim(c.from, { text: teks }, { quoted: c.msg });

// ----------------------------------------------------------------------------
// DAFTAR PERINTAH
// ----------------------------------------------------------------------------
async function cmdMenu(c) {
    const caption = buatMenu(c.nama);
    if (fs.existsSync(FILE_LOGO)) {
        await kirim(c.from, { image: fs.readFileSync(FILE_LOGO), caption }, { quoted: c.msg });
    } else {
        await balas(c, caption);
    }
}

const PERINTAH = {
    menu: cmdMenu,
    help: cmdMenu,

    // ---------------- MEDIA & KREATIF ----------------
    stiker: cmdStiker,
    s: cmdStiker,

    async toimg(c) {
        const target = ambilMedia(c.msg, c.isi, 'stickerMessage');
        if (!target) return balas(c, `${E.warn} Reply sebuah stiker dengan *!toimg*`);
        const animasi = target.message.stickerMessage.isAnimated;
        const png = await sharp(await unduh(target)).png().toBuffer();
        await kirim(c.from, {
            image: png,
            caption: `${E.check} Stiker berhasil diubah ke gambar.` +
                (animasi ? `\n${E.warn} Stiker animasi hanya diambil frame pertamanya.` : '')
        }, { quoted: c.msg });
    },

    async qr(c) {
        if (!c.args) return balas(c, `${E.warn} Contoh: *!qr https://google.com*`);
        if (c.args.length > 1000) return balas(c, `${E.warn} Teks terlalu panjang (maks 1000 karakter).`);
        const png = await QRCode.toBuffer(c.args, {
            type: 'png', width: 600, margin: 2, errorCorrectionLevel: 'M'
        });
        await kirim(c.from, { image: png, caption: `${E.qr} QR Code siap dipindai.` }, { quoted: c.msg });
    },

    async tts(c) {
        if (!c.args) return balas(c, `${E.warn} Contoh: *!tts selamat pagi semuanya*`);
        if (c.args.length > 500) return balas(c, `${E.warn} Teks terlalu panjang (maks 500 karakter).`);
        const mp3 = await buatSuara(c.args);
        let ogg;
        try {
            ogg = await keOpus(mp3);
        } catch (e) {
            console.log('[TTS] konversi gagal:', e.message);
            return balas(c, `${E.cross} Konversi suara gagal. Jalankan *npm install ffmpeg-static* di folder bot, lalu restart bot.`);
        }
        await kirim(c.from, { audio: ogg, mimetype: 'audio/ogg; codecs=opus', ptt: true }, { quoted: c.msg });
    },

    // ---------------- CATATAN PRIBADI ----------------
    async catat(c) {
        if (!c.args) return balas(c, `${E.warn} Ketik isi catatannya, contoh: *!catat beli kopi*`);
        if (c.args.length > MAKS_PANJANG_CATATAN) {
            return balas(c, `${E.warn} Catatan terlalu panjang (maks ${MAKS_PANJANG_CATATAN} karakter).`);
        }
        const data = bacaCatatan();
        const daftar = data[c.idPengirim] || [];
        if (daftar.length >= MAKS_CATATAN) {
            return balas(c, `${E.warn} Catatan penuh (maks ${MAKS_CATATAN}). Hapus beberapa dulu dengan *!hapus [nomor]*.`);
        }
        daftar.push(c.args);
        data[c.idPengirim] = daftar;
        simpanCatatan(data);
        await balas(c, `${E.check} Catatan #${daftar.length} disimpan:\n_"${c.args}"_`);
    },

    async catatan(c) {
        const daftar = bacaCatatan()[c.idPengirim] || [];
        await balas(c, daftar.length
            ? `${E.list} *CATATANMU*\n` + daftar.map((v, i) => `${i + 1}. ${v}`).join('\n') +
              `\n\n_Hapus satu: *!hapus [nomor]*_`
            : `${E.inbox} Catatanmu masih kosong. Tambah dengan *!catat [teks]*`);
    },

    async hapus(c) {
        const no = parseInt(c.args, 10);
        if (!c.args || isNaN(no)) return balas(c, `${E.warn} Contoh: *!hapus 2* (lihat nomor lewat *!catatan*)`);
        const data = bacaCatatan();
        const daftar = data[c.idPengirim] || [];
        if (no < 1 || no > daftar.length) return balas(c, `${E.warn} Nomor ${no} tidak ada. Cek *!catatan*.`);
        const [dihapus] = daftar.splice(no - 1, 1);
        if (daftar.length) data[c.idPengirim] = daftar; else delete data[c.idPengirim];
        simpanCatatan(data);
        await balas(c, `${E.trash} Catatan #${no} dihapus:\n_"${dihapus}"_`);
    },

    async hapuscatatan(c) {
        const data = bacaCatatan();
        const jumlah = (data[c.idPengirim] || []).length;
        if (!jumlah) return balas(c, `${E.inbox} Catatanmu sudah kosong.`);
        delete data[c.idPengirim];
        simpanCatatan(data);
        await balas(c, `${E.trash} ${jumlah} catatan milikmu dihapus.`);
    },

    // ---------------- ALAT & PENCARIAN ----------------
    async hitung(c) {
        if (!c.args) return balas(c, `${E.warn} Contoh: *!hitung (12+8)*5/2*\nOperator: + - * / % ^ ( )`);
        let hasil;
        try {
            hasil = hitung(c.args);
        } catch (e) {
            return balas(c, `${E.cross} ${e.message}`);
        }
        const rapi = parseFloat(hasil.toPrecision(12)).toLocaleString('id-ID', { maximumFractionDigits: 10 });
        await balas(c, `${E.calc} *KALKULATOR*\n${c.args}\n= *${rapi}*`);
    },

    async cuaca(c) {
        if (!c.args) return balas(c, `${E.warn} Contoh: *!cuaca Semarang*`);
        const d = await ambilCuaca(c.args);
        if (!d) return balas(c, `${E.cross} Kota *${c.args}* tidak ditemukan.`);
        const { lokasi: l, now: n } = d;
        const tempat = [l.name, l.admin1, l.country].filter(Boolean).join(', ');
        await balas(c, [
            `${E.globe} *${tempat}*`,
            `${E.sun} ${KODE_CUACA[n.weather_code] || 'Tidak diketahui'}`,
            `${E.temp} Suhu: *${n.temperature_2m}\u{00B0}C* (terasa ${n.apparent_temperature}\u{00B0}C)`,
            `${E.drop} Kelembapan: *${n.relative_humidity_2m}%*`,
            `${E.wind} Angin: *${n.wind_speed_10m} km/jam*`
        ].join('\n'));
    },

    async kurs(c) {
        const jumlah = c.args ? parseAngka(c.args) : 1;
        if (isNaN(jumlah) || jumlah <= 0 || jumlah > 1e12) {
            return balas(c, `${E.warn} Contoh: *!kurs 100* atau *!kurs 1.5*`);
        }
        const { rate, waktu } = await ambilKurs();
        const fmt = (v, d = 2) => v.toLocaleString('id-ID', { maximumFractionDigits: d });
        await balas(c, [
            `${E.money} *KONVERSI USD KE IDR*`,
            `$${fmt(jumlah)} = *Rp${fmt(jumlah * rate)}*`,
            '',
            `_Kurs: 1 USD = Rp${fmt(rate)}_`,
            `_Diperbarui: ${waktu || '-'}_`
        ].join('\n'));
    },

    async singkat(c) {
        if (!c.args) return balas(c, `${E.warn} Contoh: *!singkat https://contoh.com/halaman/panjang*`);
        let url;
        try {
            url = new URL(/^https?:\/\//i.test(c.args) ? c.args : `https://${c.args}`);
            if (!['http:', 'https:'].includes(url.protocol)) throw new Error();
        } catch {
            return balas(c, `${E.cross} URL tidak valid.`);
        }
        const hasil = (await ambilResponse(
            `https://tinyurl.com/api-create.php?url=${encodeURIComponent(url.href)}`, 'text'
        )).trim();
        if (!/^https?:\/\//.test(hasil)) throw new Error('Respon TinyURL tidak valid');
        await balas(c, `${E.link} *Link dipendekkan*\n${hasil}`);
    },

    async wiki(c) {
        if (!c.args) return balas(c, `${E.warn} Contoh: *!wiki Candi Borobudur*`);
        const d = await cariWiki(c.args);
        if (!d?.extract) return balas(c, `${E.cross} Tidak ada hasil untuk *${c.args}*.`);
        let ringkas = d.extract;
        if (ringkas.length > 800) {
            ringkas = ringkas.slice(0, 800);
            const titik = ringkas.lastIndexOf('. ');
            ringkas = (titik > 300 ? ringkas.slice(0, titik + 1) : ringkas) + (titik > 300 ? '' : '...');
        }
        const tautan = d.content_urls?.desktop?.page;
        await balas(c, `${E.book} *${d.title}*\n\n${ringkas}` + (tautan ? `\n\n${E.link} ${tautan}` : ''));
    },

    // ---------------- HIBURAN & STATUS ----------------
    async quotes(c) {
        await balas(c, `${E.spark} *KUTIPAN HARI INI*\n\n_"${pilihAcak(QUOTES)}"_`);
    },

    async fakta(c) {
        await balas(c, `${E.bulb} *FAKTA UNIK*\n\n${pilihAcak(FAKTA)}`);
    },

    async gacha(c) {
        // Hasil tetap sepanjang hari (WIB) untuk tiap nomor, berganti besok
        const tanggal = new Date().toLocaleDateString('en-CA', { timeZone: 'Asia/Jakarta' });
        const hash = crypto.createHash('sha256').update(`${c.idPengirim}|${tanggal}`).digest();
        const persen = hash.readUInt32BE(0) % 101;
        const penuh = Math.round(persen / 10);
        const bar = B.FULL.repeat(penuh) + B.EMPTY.repeat(10 - penuh);
        const komentar =
            persen >= 90 ? 'Hoki luar biasa! Waktunya coba keberuntungan.' :
            persen >= 70 ? 'Hari yang bagus, manfaatkan!' :
            persen >= 40 ? 'Lumayan, biasa saja.' :
            persen >= 20 ? 'Agak kurang hoki, hati-hati ya.' :
                           'Hari ini mending santai dulu.';
        await balas(c, `${E.clover} *GACHA HOKI HARIAN*\n${c.nama}\n\n${bar} *${persen}%*\n_${komentar}_`);
    },

    async jodoh(c) {
        const pisah = /[&+]/.test(c.args) ? /\s*[&+]\s*/ : /\s+(?:dan|x)\s+/i;
        const nama = c.args.split(pisah).map(bersihkanNama).filter(Boolean);
        if (nama.length !== 2 || nama.some((n) => n.length > 30)) {
            return balas(c, `${E.warn} Contoh: *!jodoh Budi & Ani*\n_(pisahkan dua nama dengan &, +, atau "dan")_`);
        }
        const r = hitungJodoh(nama[0], nama[1]);
        await balas(c, [
            `${E.hearts} *CEK JODOH*`,
            `*${nama[0]}* ${E.heart} *${nama[1]}*`,
            '',
            `${bar10(r.persen)} *${r.persen}%*`,
            `${E.cupid} Cinta: *${r.cinta}%*`,
            `${E.speech} Komunikasi: *${r.komunikasi}%*`,
            `${E.handshake} Kesetiaan: *${r.kesetiaan}%*`,
            '',
            `_${komentarJodoh(r.persen, r.sama)}_`,
            '_Hanya hiburan, jangan baper ya!_'
        ].join('\n'));
    },

    async zodiak(c) {
        const tgl = c.args ? parseDuaTanggal(c.args) : null;
        if (!tgl) {
            return balas(c, `${E.warn} Contoh: *!zodiak 14-2 20-8*\n_(tanggal-bulan orang pertama lalu orang kedua)_`);
        }
        const [z1, z2] = tgl.map((t) => cariZodiak(t.hari, t.bulan));
        const skor = hitungZodiak(z1, z2);
        const komentar =
            skor >= 80 ? 'Bintang kalian sangat searah!' :
            skor >= 60 ? 'Cukup harmonis, saling melengkapi.' :
            skor >= 40 ? 'Perlu banyak kompromi, tapi bukan mustahil.' :
                         'Sering beda pendapat, sabar-sabar ya.';
        await balas(c, [
            `${E.crystal} *KECOCOKAN ZODIAK*`,
            `${TANDA[z1][0]} *${z1}* (${TANDA[z1][1]})`,
            `${TANDA[z2][0]} *${z2}* (${TANDA[z2][1]})`,
            '',
            `${bar10(skor)} *${skor}%*`,
            `_${komentar}_`,
            '_Hanya hiburan, jangan baper ya!_'
        ].join('\n'));
    },

    async ingatkan(c) {
        const contoh = `${E.warn} Contoh:\n*!ingatkan 30m minum obat*\n*!ingatkan 2j rapat*\n*!ingatkan 1j30m jemput adik*\n_(satuan: m/menit, j/jam, hari)_`;
        const p = parseWaktuPengingat(c.args);
        if (!p || !p.pesan) return balas(c, contoh);
        if (p.ms < 60000) return balas(c, `${E.warn} Waktu minimal 1 menit.`);
        if (p.ms > MAKS_HARI_PENGINGAT * 86400000) {
            return balas(c, `${E.warn} Waktu maksimal ${MAKS_HARI_PENGINGAT} hari.`);
        }
        if (p.pesan.length > 300) return balas(c, `${E.warn} Pesan pengingat maksimal 300 karakter.`);

        const data = bacaPengingat();
        if (data.filter((x) => x.idPengirim === c.idPengirim).length >= MAKS_PENGINGAT) {
            return balas(c, `${E.warn} Pengingat aktif sudah penuh (maks ${MAKS_PENGINGAT}). Batalkan dulu dengan *!batalingat [nomor]*.`);
        }
        const waktu = Date.now() + p.ms;
        data.push({ id: crypto.randomUUID(), jid: c.from, idPengirim: c.idPengirim, waktu, pesan: p.pesan, gagal: 0 });
        simpanPengingat(data);
        await balas(c, `${E.bell} Siap! Saya ingatkan dalam *${formatDurasi(p.ms, true)}*\n(${formatWaktuWIB(waktu)})\n_"${p.pesan}"_`);
    },

    async pengingat(c) {
        const milik = bacaPengingat().filter((x) => x.idPengirim === c.idPengirim).sort((a, b) => a.waktu - b.waktu);
        if (!milik.length) return balas(c, `${E.inbox} Tidak ada pengingat aktif. Buat dengan *!ingatkan 30m [pesan]*`);
        await balas(c, `${E.bell} *PENGINGATMU*\n` +
            milik.map((x, i) => `${i + 1}. ${x.pesan}\n    _${formatWaktuWIB(x.waktu)}_`).join('\n') +
            '\n\n_Batalkan: *!batalingat [nomor]*_');
    },

    async batalingat(c) {
        const no = parseInt(c.args, 10);
        const data = bacaPengingat();
        const milik = data.filter((x) => x.idPengirim === c.idPengirim).sort((a, b) => a.waktu - b.waktu);
        if (!c.args || isNaN(no)) return balas(c, `${E.warn} Contoh: *!batalingat 1* (lihat nomor lewat *!pengingat*)`);
        if (no < 1 || no > milik.length) return balas(c, `${E.warn} Nomor ${no} tidak ada. Cek *!pengingat*.`);
        const target = milik[no - 1];
        simpanPengingat(data.filter((x) => x.id !== target.id));
        await balas(c, `${E.trash} Pengingat #${no} dibatalkan:\n_"${target.pesan}"_`);
    },

    async sholat(c) {
        if (!c.args) return balas(c, `${E.warn} Contoh: *!sholat Semarang*`);
        const d = await ambilJadwalSholat(c.args);
        if (!d) return balas(c, `${E.cross} Kota *${c.args}* tidak ditemukan.`);
        const tempat = [d.lokasi.name, d.lokasi.admin1, d.lokasi.country].filter(Boolean).join(', ');
        const baris = d.lima.map((x) => `${x.nama === d.berikut ? B.R : ' '} ${x.nama.padEnd(8)} *${x.jam}*` +
            (x.nama === d.berikut ? '  _(berikutnya)_' : ''));
        baris.splice(1, 0, `  Terbit   *${d.terbit}*`);
        await balas(c, [
            `${E.mosque} *JADWAL SHOLAT*`,
            `${E.globe} ${tempat}`,
            `${E.clock} ${d.tanggal} (${d.zona})`,
            '',
            ...baris,
            '',
            `_${d.kemenag ? 'Metode Kemenag RI. ' : ''}Sebagai acuan, bisa selisih 1-2 menit dari jadwal masjid setempat._`
        ].join('\n'));
    },

    status: cmdStatus,
    ping: cmdStatus
};

async function cmdStiker(c) {
    const target = ambilMedia(c.msg, c.isi, 'imageMessage');
    if (!target) {
        return balas(c, `${E.warn} Kirim foto dengan caption *!stiker*, atau reply foto dengan *!stiker*`);
    }
    const webp = await sharp(await unduh(target))
        .resize(512, 512, { fit: 'contain', background: { r: 0, g: 0, b: 0, alpha: 0 } })
        .ensureAlpha()
        .webp({ quality: 80 })
        .toBuffer();
    await kirim(c.from, { sticker: webp }, { quoted: c.msg });
}

async function cmdStatus(c) {
    const t0 = Date.now();
    const terkirim = await kirim(c.from, { text: `${E.ping} Mengukur...` }, { quoted: c.msg });
    const ms = Date.now() - t0;
    const kondisi = ms < 800 ? 'Cepat' : ms < 2000 ? 'Normal' : 'Lambat';
    const teks = [
        `${E.chart} *STATUS BOT*`,
        `${E.clock} Waktu: *${sekarangWIB()}*`,
        `${E.ping} Respon: *${ms} ms* (${kondisi})`,
        `${E.up} Aktif: *${formatDurasi(process.uptime() * 1000)}*`
    ].join('\n');
    try {
        await kirim(c.from, { text: teks, edit: terkirim.key });
    } catch {
        await balas(c, teks);
    }
}

// ----------------------------------------------------------------------------
// PENANGANAN PESAN MASUK
// ----------------------------------------------------------------------------
async function tangani(msg) {
    if (!msg.message || !msg.key?.id) return;

    // Abaikan pesan yang barusan dikirim oleh bot sendiri
    if (sentIds.has(msg.key.id)) {
        sentIds.delete(msg.key.id);
        return;
    }

    const from = msg.key.remoteJid;
    if (!from || from === 'status@broadcast' || from.endsWith('@broadcast') || from.endsWith('@newsletter')) return;

    const me = !!msg.key.fromMe;
    const grup = from.endsWith('@g.us');

    // KEAMANAN: diam total di grup, kecuali nomor bot sendiri yang mengetik perintah
    if (grup && !me) return;

    const isi = bukaPesan(msg.message);
    if (!isi || isi.protocolMessage || isi.reactionMessage || isi.senderKeyDistributionMessage) return;

    const teks = ambilTeks(isi);
    const pengirimJid = me ? (sock.user?.id || '') : (msg.key.participant || from);
    const idPengirim = pengirimJid.split('@')[0].split(':')[0].replace(/\D/g, '') || 'tidak_dikenal';
    const nama = msg.pushName || idPengirim;

    // ---------- Perintah ----------
    if (teks.startsWith(PREFIX)) {
        const spasi = teks.search(/\s/);
        const cmd = teks.slice(PREFIX.length, spasi < 0 ? undefined : spasi).toLowerCase();
        const args = spasi < 0 ? '' : teks.slice(spasi).trim();

        if (cmd) {
            const handler = Object.hasOwn(PERINTAH, cmd) ? PERINTAH[cmd] : null;
            const c = { msg, from, isi, teks, args, idPengirim, nama, me };

            if (!handler) {
                if (!me) await balas(c, `${E.cross} Perintah *${PREFIX}${cmd}* tidak dikenal. Ketik *${PREFIX}menu* untuk daftar perintah.`);
                return;
            }

            // Anti-spam: jeda antar perintah (tidak berlaku untuk nomor bot sendiri)
            if (!me) {
                const terakhir = cooldown.get(idPengirim) || 0;
                if (Date.now() - terakhir < COOLDOWN_MS) return;
                cooldown.set(idPengirim, Date.now());
                if (cooldown.size > 1000) cooldown.clear();
            }

            console.log(`[CMD] ${nama} (+${idPengirim}): ${teks.slice(0, 80)}`);
            try {
                await handler(c);
            } catch (e) {
                console.log(`[ERROR ${PREFIX}${cmd}]`, e.message);
                await balas(c, `${E.cross} Terjadi kesalahan saat memproses *${PREFIX}${cmd}*. Coba lagi nanti.`).catch(() => {});
            }
            return;
        }
    }

    // ---------- Chat pribadi non-perintah -> antrean terminal ----------
    if (me) return;

    const nomor = from.split('@')[0];
    const pesan = teks || jenisMedia(isi);
    const ada = antreanChat.findIndex((x) => x.jid === from);
    if (ada !== -1) {
        antreanChat[ada].pesan = pesan;
        antreanChat[ada].nama = nama;
        antreanChat[ada].jumlah++;
    } else {
        antreanChat.push({ jid: from, nama, nomor, pesan, jumlah: 1 });
        if (antreanChat.length > MAKS_ANTREAN) antreanChat.shift();
    }
    console.log(`\n[CHAT MASUK] ${nama} (+${nomor}): "${pesan.slice(0, 100)}"\nKetik "list" di terminal untuk membalas.`);
}

// ----------------------------------------------------------------------------
// KONTROL TERMINAL CMD: antrean balas manual
// ----------------------------------------------------------------------------
async function menuTerminal() {
    while (true) {
        const input = (await tanya('\n[Terminal] Ketik "list": ')).trim().toLowerCase();
        if (input !== 'list') continue;

        if (!antreanChat.length) {
            console.log('Belum ada chat masuk.');
            continue;
        }

        console.log('\n=== DAFTAR CHAT ===');
        antreanChat.forEach((c, i) => {
            const jml = c.jumlah > 1 ? ` (${c.jumlah} pesan)` : '';
            console.log(`[${i + 1}] ${c.nama} (+${c.nomor})${jml} -> "${c.pesan.slice(0, 80)}"`);
        });

        const pilih = parseInt(await tanya('Pilih nomor urut (0 batal): '), 10) - 1;
        if (isNaN(pilih) || pilih < 0 || pilih >= antreanChat.length) {
            console.log('Batal.');
            continue;
        }

        const target = antreanChat[pilih];
        console.log(
            `\nBalas ke ${target.nama}:\n` +
            ' [1] Bentar ya, lagi di jalan\n' +
            ' [2] Oke siap, noted!\n' +
            ' [3] Lagi sibuk dikit, nanti dikabarin\n' +
            ' [Ketik bebas] Langsung ketik pesan'
        );
        const jwb = (await tanya('Pilihan/Pesan: ')).trim();
        const balasan =
            jwb === '1' ? 'Bentar ya, lagi di jalan.' :
            jwb === '2' ? 'Oke siap, noted!' :
            jwb === '3' ? 'Lagi sibuk dikit, nanti dikabarin.' : jwb;

        if (!balasan) {
            console.log('Batal.');
            continue;
        }
        try {
            await kirim(target.jid, { text: balasan });
            console.log(`Terkirim ke ${target.nama}!`);
            antreanChat.splice(antreanChat.findIndex((x) => x.jid === target.jid), 1);
        } catch (e) {
            console.log('Gagal mengirim:', e.message);
        }
    }
}

// ----------------------------------------------------------------------------
// KONEKSI
// ----------------------------------------------------------------------------
async function mintaPairing() {
    if (pairingBerjalan) return;
    pairingBerjalan = true;
    try {
        console.log('\nSesi baru terdeteksi. Hubungkan menggunakan Nomor HP (Pairing Code).');
        const input = await tanya('Masukkan nomor WhatsApp Anda (awalan 62, contoh 628123456789): ');
        const nomor = input.replace(/[^0-9]/g, '');
        await new Promise((r) => setTimeout(r, 3000));
        const kode = await sock.requestPairingCode(nomor);
        console.log(`\nKODE PAIRING ANDA: ${kode}`);
        console.log('Buka WhatsApp di HP > Perangkat Tertaut > Tautkan Perangkat > Tautkan dengan nomor telepon saja!\n');
    } catch (err) {
        console.log('Gagal meminta kode pairing:', err.message);
    } finally {
        pairingBerjalan = false;
    }
}

async function jalankanBot() {
    const { state, saveCreds } = await useMultiFileAuthState(FOLDER_SESI);
    const { version } = await fetchLatestBaileysVersion();

    sock = makeWASocket({
        version,
        auth: state,
        logger,
        browser: ['Ubuntu', 'Chrome', '20.0.04']
    });

    if (!sock.authState.creds.registered) mintaPairing();

    sock.ev.on('creds.update', saveCreds);

    sock.ev.on('connection.update', ({ connection, lastDisconnect }) => {
        if (connection === 'close') {
            terhubung = false;
            const code = new Boom(lastDisconnect?.error)?.output?.statusCode;
            if (code === DisconnectReason.loggedOut) {
                console.log(`\nSesi logout. Hapus folder "${FOLDER_SESI}" lalu jalankan ulang bot.`);
                process.exit(0);
            }
            console.log(`\nKoneksi terputus (kode ${code ?? '?'}). Menyambung ulang...`);
            setTimeout(jalankanBot, 3000);
        } else if (connection === 'open') {
            terhubung = true;
            jalankanPengingat();
            console.log('\nBOT AKTIF! Ketik "list" di terminal untuk membalas chat masuk.\n');
            if (!terminalAktif) {
                terminalAktif = true;
                menuTerminal();
            }
        }
    });

    sock.ev.on('messages.upsert', async ({ messages, type }) => {
        if (type !== 'notify') return;
        for (const msg of messages) {
            try {
                await tangani(msg);
            } catch (e) {
                console.log('[ERROR PESAN]', e.message);
            }
        }
    });
}

process.on('unhandledRejection', (e) => console.log('[UNHANDLED]', e?.message || e));
process.on('uncaughtException', (e) => console.log('[UNCAUGHT]', e?.message || e));

siapkanFileCatatan();
siapkanFilePengingat();
jalankanBot();