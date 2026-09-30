#!/usr/bin/env python3
"""Space quiz room server: static files + one in-memory game room.

Run: python3 server.py [port]   (defaults to 8765, listens on 0.0.0.0)
Standard library only.
"""

import json
import os
import socket
import subprocess
import sys
import threading
import time
import uuid
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse

ROOT = os.path.dirname(os.path.abspath(__file__))
PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 8765
ACTIVE_SECONDS = 12
MAX_NAME = 16
MAX_PLAYERS = 12


# ---------------------------------------------------------------- QR code
# Byte mode, error correction level M, versions 1-6 (enough for ~100 bytes).

ECC_M_PER_BLOCK = [None, 10, 16, 26, 18, 24, 16]
ECC_M_BLOCKS = [None, 1, 1, 1, 2, 2, 4]


def _gf_mul(x, y):
    z = 0
    for i in range(7, -1, -1):
        z = (z << 1) ^ ((z >> 7) * 0x11D)
        z ^= ((y >> i) & 1) * x
    return z


def _rs_divisor(degree):
    result = [0] * (degree - 1) + [1]
    root = 1
    for _ in range(degree):
        for j in range(degree):
            result[j] = _gf_mul(result[j], root)
            if j + 1 < degree:
                result[j] ^= result[j + 1]
        root = _gf_mul(root, 0x02)
    return result


def _rs_remainder(data, divisor):
    result = [0] * len(divisor)
    for b in data:
        factor = b ^ result.pop(0)
        result.append(0)
        for i, coef in enumerate(divisor):
            result[i] ^= _gf_mul(coef, factor)
    return result


def _raw_codewords(ver):
    modules = (16 * ver + 128) * ver + 64
    if ver >= 2:
        align = ver // 7 + 2
        modules -= (25 * align - 10) * align - 55
    return modules // 8


def qr_matrix(text):
    data = text.encode('utf-8')
    for ver in range(1, 7):
        raw = _raw_codewords(ver)
        data_cw = raw - ECC_M_PER_BLOCK[ver] * ECC_M_BLOCKS[ver]
        if 4 + 8 + 8 * len(data) <= data_cw * 8:
            break
    else:
        raise ValueError('text too long for QR')

    bits = []

    def put(value, length):
        for i in range(length - 1, -1, -1):
            bits.append((value >> i) & 1)

    put(0b0100, 4)
    put(len(data), 8)
    for b in data:
        put(b, 8)
    capacity = data_cw * 8
    put(0, min(4, capacity - len(bits)))
    put(0, (8 - len(bits) % 8) % 8)
    pad = 0xEC
    while len(bits) < capacity:
        put(pad, 8)
        pad ^= 0xEC ^ 0x11
    codewords = [int(''.join(map(str, bits[i:i + 8])), 2) for i in range(0, len(bits), 8)]

    num_blocks = ECC_M_BLOCKS[ver]
    ecc_len = ECC_M_PER_BLOCK[ver]
    short_count = num_blocks - raw % num_blocks
    short_len = raw // num_blocks
    divisor = _rs_divisor(ecc_len)
    blocks = []
    k = 0
    for i in range(num_blocks):
        size = short_len - ecc_len + (0 if i < short_count else 1)
        chunk = codewords[k:k + size]
        k += size
        blocks.append((chunk, _rs_remainder(chunk, divisor)))
    stream = []
    for i in range(max(len(b[0]) for b in blocks)):
        for chunk, _ in blocks:
            if i < len(chunk):
                stream.append(chunk[i])
    for i in range(ecc_len):
        for _, ecc in blocks:
            stream.append(ecc[i])

    n = 17 + 4 * ver
    mods = [[False] * n for _ in range(n)]
    func = [[False] * n for _ in range(n)]

    def setf(x, y, dark):
        mods[y][x] = dark
        func[y][x] = True

    for i in range(n):
        setf(6, i, i % 2 == 0)
        setf(i, 6, i % 2 == 0)
    for cx, cy in ((3, 3), (n - 4, 3), (3, n - 4)):
        for dy in range(-4, 5):
            for dx in range(-4, 5):
                x, y = cx + dx, cy + dy
                if 0 <= x < n and 0 <= y < n:
                    setf(x, y, max(abs(dx), abs(dy)) not in (2, 4))
    if ver >= 2:
        a = n - 7
        for dy in range(-2, 3):
            for dx in range(-2, 3):
                setf(a + dx, a + dy, max(abs(dx), abs(dy)) != 1)

    def draw_format(mask):
        value = (0 << 3) | mask  # ECC level M = 0b00
        rem = value
        for _ in range(10):
            rem = (rem << 1) ^ ((rem >> 9) * 0x537)
        fmt = ((value << 10) | rem) ^ 0x5412
        bit = lambda i: ((fmt >> i) & 1) == 1
        for i in range(6):
            setf(8, i, bit(i))
        setf(8, 7, bit(6))
        setf(8, 8, bit(7))
        setf(7, 8, bit(8))
        for i in range(9, 15):
            setf(14 - i, 8, bit(i))
        for i in range(8):
            setf(n - 1 - i, 8, bit(i))
        for i in range(8, 15):
            setf(8, n - 15 + i, bit(i))
        setf(8, n - 8, True)

    draw_format(0)

    i = 0
    total_bits = len(stream) * 8
    right = n - 1
    while right >= 1:
        if right == 6:
            right = 5
        for vert in range(n):
            for j in range(2):
                x = right - j
                upward = ((right + 1) & 2) == 0
                y = n - 1 - vert if upward else vert
                if not func[y][x] and i < total_bits:
                    mods[y][x] = ((stream[i >> 3] >> (7 - (i & 7))) & 1) == 1
                    i += 1
        right -= 2

    masks = [
        lambda x, y: (x + y) % 2 == 0,
        lambda x, y: y % 2 == 0,
        lambda x, y: x % 3 == 0,
        lambda x, y: (x + y) % 3 == 0,
        lambda x, y: (x // 3 + y // 2) % 2 == 0,
        lambda x, y: x * y % 2 + x * y % 3 == 0,
        lambda x, y: (x * y % 2 + x * y % 3) % 2 == 0,
        lambda x, y: ((x + y) % 2 + x * y % 3) % 2 == 0,
    ]

    def apply_mask(m):
        fn = masks[m]
        for y in range(n):
            for x in range(n):
                if not func[y][x] and fn(x, y):
                    mods[y][x] = not mods[y][x]

    def penalty():
        score = 0
        lines = [row for row in mods] + [[mods[y][x] for y in range(n)] for x in range(n)]
        for line in lines:
            run = 1
            for k2 in range(1, n + 1):
                if k2 < n and line[k2] == line[k2 - 1]:
                    run += 1
                else:
                    if run >= 5:
                        score += run - 2
                    run = 1
        for y in range(n - 1):
            for x in range(n - 1):
                c = mods[y][x]
                if c == mods[y][x + 1] == mods[y + 1][x] == mods[y + 1][x + 1]:
                    score += 3
        dark = sum(sum(1 for c in row if c) for row in mods)
        score += abs(dark * 20 - n * n * 10) // (n * n) * 10
        return score

    best, best_score = 0, None
    for m in range(8):
        apply_mask(m)
        draw_format(m)
        s = penalty()
        if best_score is None or s < best_score:
            best, best_score = m, s
        apply_mask(m)
    apply_mask(best)
    draw_format(best)
    return mods


def qr_svg(text, border=4):
    mods = qr_matrix(text)
    n = len(mods)
    size = n + border * 2
    parts = []
    for y in range(n):
        for x in range(n):
            if mods[y][x]:
                parts.append('M%d,%dh1v1h-1z' % (x + border, y + border))
    return (
        '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 %d %d" shape-rendering="crispEdges">'
        '<rect width="100%%" height="100%%" fill="#ffffff"/>'
        '<path d="%s" fill="#0b1026"/></svg>' % (size, size, ''.join(parts))
    )


# ---------------------------------------------------------------- network

def lan_ip():
    for iface in ('en0', 'en1'):
        try:
            out = subprocess.run(['ipconfig', 'getifaddr', iface], capture_output=True, text=True, timeout=2)
            ip = out.stdout.strip()
            if ip and not ip.startswith('127.'):
                return ip
        except Exception:
            pass
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(('10.255.255.255', 1))
        ip = s.getsockname()[0]
        s.close()
        return ip
    except Exception:
        return '127.0.0.1'


JOIN_URL = 'http://%s:%d/join' % (lan_ip(), PORT)
QR_SVG = qr_svg(JOIN_URL)


# ---------------------------------------------------------------- room

LOCK = threading.Lock()
ROOM = {
    'phase': 'lobby',      # lobby | question | reveal | results
    'round': 0,
    'players': {},         # id -> {name, score, seen, joined}
    'q': 0,
    'total': 0,
    'question': None,      # {text, answers}
    'correct': None,
    'answers': {},         # player id -> choice index
    'deadline': 0,
}


def _active(now):
    return [
        (pid, p) for pid, p in ROOM['players'].items()
        if now - p['seen'] <= ACTIVE_SECONDS
    ]


def room_state(viewer=None):
    now = time.time()
    if viewer and viewer in ROOM['players']:
        ROOM['players'][viewer]['seen'] = now
    active = sorted(_active(now), key=lambda item: item[1]['joined'])
    reveal = ROOM['phase'] in ('reveal', 'results')
    state = {
        'phase': ROOM['phase'],
        'round': ROOM['round'],
        'joinUrl': JOIN_URL,
        'q': ROOM['q'],
        'total': ROOM['total'],
        'question': ROOM['question'],
        'deadlineIn': max(0, ROOM['deadline'] - now) if ROOM['phase'] == 'question' else 0,
        'players': [
            {
                'id': pid,
                'name': p['name'],
                'score': p['score'],
                'answered': pid in ROOM['answers'],
                'choice': ROOM['answers'].get(pid) if reveal else None,
            }
            for pid, p in active
        ],
        'correct': ROOM['correct'] if ROOM['phase'] == 'reveal' else None,
    }
    if viewer:
        me = ROOM['players'].get(viewer)
        state['me'] = None if me is None else {
            'id': viewer,
            'name': me['name'],
            'score': me['score'],
            'choice': ROOM['answers'].get(viewer),
        }
    return state


def api(path, body):
    now = time.time()
    if path == '/api/join':
        name = ' '.join(str(body.get('name', '')).split())[:MAX_NAME]
        if not name:
            return 400, {'error': 'Введите имя'}
        pid = str(body.get('id') or '')
        if pid in ROOM['players']:
            ROOM['players'][pid]['name'] = name
            ROOM['players'][pid]['seen'] = now
        else:
            if len(_active(now)) >= MAX_PLAYERS:
                return 409, {'error': 'Комната заполнена'}
            pid = uuid.uuid4().hex[:10]
            ROOM['players'][pid] = {'name': name, 'score': 0, 'seen': now, 'joined': now}
        return 200, room_state(pid)

    if path == '/api/lobby':
        for p in ROOM['players'].values():
            p['score'] = 0
        ROOM.update(phase='lobby', q=0, total=0, question=None, correct=None, answers={}, deadline=0)
        ROOM['round'] += 1
        return 200, room_state()

    if path == '/api/start':
        if not _active(now):
            return 409, {'error': 'Нет игроков'}
        for p in ROOM['players'].values():
            p['score'] = 0
        ROOM['round'] += 1
        ROOM.update(phase='starting', q=0, total=int(body.get('total') or 0),
                    question=None, correct=None, answers={}, deadline=0)
        return 200, room_state()

    if path == '/api/question':
        try:
            answers = [str(a) for a in body['answers']][:4]
            correct = int(body['correct'])
        except (KeyError, TypeError, ValueError):
            return 400, {'error': 'bad question'}
        ROOM.update(
            phase='question',
            q=int(body.get('q') or 0),
            total=int(body.get('total') or ROOM['total']),
            question={'text': str(body.get('text', '')), 'answers': answers},
            correct=correct,
            answers={},
            deadline=now + float(body.get('seconds') or 20),
        )
        return 200, room_state()

    if path == '/api/answer':
        pid = str(body.get('id') or '')
        if pid not in ROOM['players']:
            return 404, {'error': 'Игрок не найден'}
        ROOM['players'][pid]['seen'] = now
        if ROOM['phase'] != 'question' or int(body.get('q', -1)) != ROOM['q']:
            return 409, {'error': 'Сейчас нельзя ответить'}
        if pid in ROOM['answers']:
            return 200, room_state(pid)
        try:
            choice = int(body.get('choice'))
        except (TypeError, ValueError):
            return 400, {'error': 'bad choice'}
        if not 0 <= choice < len(ROOM['question']['answers']):
            return 400, {'error': 'bad choice'}
        ROOM['answers'][pid] = choice
        return 200, room_state(pid)

    if path == '/api/reveal':
        if ROOM['phase'] == 'question':
            for pid, choice in ROOM['answers'].items():
                if choice == ROOM['correct'] and pid in ROOM['players']:
                    ROOM['players'][pid]['score'] += 1
            ROOM['phase'] = 'reveal'
        return 200, room_state()

    if path == '/api/finish':
        ROOM['phase'] = 'results'
        return 200, room_state()

    return 404, {'error': 'unknown endpoint'}


# ---------------------------------------------------------------- http

class Handler(SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=ROOT, **kwargs)

    def log_message(self, fmt, *args):
        if args and '/api/state' in str(args[0]):
            return
        super().log_message(fmt, *args)

    def end_headers(self):
        self.send_header('Cache-Control', 'no-store')
        self.send_header('Access-Control-Allow-Origin', '*')
        super().end_headers()

    def do_OPTIONS(self):
        self.send_response(204)
        self.send_header('Access-Control-Allow-Methods', 'GET, POST, OPTIONS')
        self.send_header('Access-Control-Allow-Headers', 'Content-Type')
        self.send_header('Content-Length', '0')
        self.end_headers()

    def _send(self, code, payload, ctype='application/json; charset=utf-8'):
        data = payload if isinstance(payload, bytes) else json.dumps(payload, ensure_ascii=False).encode('utf-8')
        self.send_response(code)
        self.send_header('Content-Type', ctype)
        self.send_header('Content-Length', str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def do_GET(self):
        url = urlparse(self.path)
        path = url.path
        if path == '/api/state':
            query = dict(p.split('=', 1) for p in url.query.split('&') if '=' in p)
            with LOCK:
                self._send(200, room_state(query.get('id')))
            return
        if path == '/api/qr.svg':
            self._send(200, QR_SVG.encode('utf-8'), 'image/svg+xml')
            return
        if path in ('/join', '/join/'):
            self.path = '/join.html'
        elif path == '/':
            self.path = '/index.html'
        super().do_GET()

    def do_POST(self):
        path = urlparse(self.path).path
        length = int(self.headers.get('Content-Length') or 0)
        if length > 4096:
            self._send(413, {'error': 'too large'})
            return
        raw = self.rfile.read(length) if length else b''
        try:
            body = json.loads(raw.decode('utf-8')) if raw else {}
            if not isinstance(body, dict):
                raise ValueError
        except ValueError:
            self._send(400, {'error': 'bad json'})
            return
        with LOCK:
            code, payload = api(path, body)
        self._send(code, payload)


def main():
    server = ThreadingHTTPServer(('0.0.0.0', PORT), Handler)
    server.daemon_threads = True
    print('ТВ:      http://127.0.0.1:%d/' % PORT, flush=True)
    print('Телефон: %s' % JOIN_URL, flush=True)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == '__main__':
    main()
