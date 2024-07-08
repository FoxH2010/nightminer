import base64
import binascii
import json
import hashlib
import hmac
import math
import socket
import struct
import sys
import threading
import time
from urllib.parse import urlparse

USER_AGENT = "NightMiner"
VERSION = [0, 1]

ALGORITHM_SCRYPT = 'scrypt'
ALGORITHM_SHA256D = 'sha256d'

ALGORITHMS = [ALGORITHM_SCRYPT, ALGORITHM_SHA256D]

QUIET = False
DEBUG = False
DEBUG_PROTOCOL = False

LEVEL_PROTOCOL = 'protocol'
LEVEL_INFO = 'info'
LEVEL_DEBUG = 'debug'
LEVEL_ERROR = 'error'

SCRYPT_LIBRARY_AUTO = 'auto'
SCRYPT_LIBRARY_LTC = 'ltc_scrypt (https://github.com/forrestv/p2pool)'
SCRYPT_LIBRARY_SCRYPT = 'scrypt (https://pypi.python.org/pypi/scrypt/)'
SCRYPT_LIBRARY_PYTHON = 'pure python'
SCRYPT_LIBRARIES = [SCRYPT_LIBRARY_AUTO, SCRYPT_LIBRARY_LTC, SCRYPT_LIBRARY_SCRYPT, SCRYPT_LIBRARY_PYTHON]

def log(message, level):

    global DEBUG
    global DEBUG_PROTOCOL
    global QUIET

    if QUIET and level != LEVEL_ERROR:
        return
    if not DEBUG_PROTOCOL and level == LEVEL_PROTOCOL:
        return
    if not DEBUG and level == LEVEL_DEBUG:
        return

    if level != LEVEL_PROTOCOL:
        message = '[%s] %s' % (level.upper(), message)

    print("[%s] %s" % (time.strftime("%Y-%m-%d %H:%M:%S"), message))

hexlify = binascii.hexlify
unhexlify = binascii.unhexlify

def sha256d(message):

    return hashlib.sha256(hashlib.sha256(message).digest()).digest()

def swap_endian_word(hex_word):

    message = unhexlify(hex_word)
    if len(message) != 4:
        raise ValueError('Must be 4-byte word')
    return message[::-1]

def swap_endian_words(hex_words):

    message = unhexlify(hex_words)
    if len(message) % 4 != 0:
        raise ValueError('Must be 4-byte word aligned')
    return b''.join([message[4 * i: 4 * i + 4][::-1] for i in range(0, len(message) // 4)])

def human_readable_hashrate(hashrate):

    if hashrate < 1000:
        return '%2f hashes/s' % hashrate
    if hashrate < 10000000:
        return '%2f khashes/s' % (hashrate / 1000)
    if hashrate < 10000000000:
        return '%2f Mhashes/s' % (hashrate / 1000000)
    return '%2f Ghashes/s' % (hashrate / 1000000000)

def scrypt(password, salt, N, r, p, dkLen):
    """Returns the result of the scrypt password-based key derivation function.

       This is used as the foundation of the proof-of-work for litecoin and other
       scrypt-based coins, using the parameters:
         password = block_header
         salt     = block_header
         N        = 1024
         r        = 1
         p        = 1
         dkLen    = 256 bits (=32 bytes)

       Please note, that this is a pure Python implementation, and is slow. VERY
       slow. It is meant only for completeness of a pure-Python, one file stratum
       server for Litecoin.

       I have included the ltc_scrypt C-binding from p2pool (https://github.com/forrestv/p2pool)
       which is several thousand times faster. The server will automatically attempt to load
       the faster module (use set_scrypt_library to choose a specific library).
    """

    def array_overwrite(source, source_start, dest, dest_start, length):

        for i in range(length):
            dest[dest_start + i] = source[source_start + i]

    def blockxor(source, source_start, dest, dest_start, length):

        for i in range(length):
            dest[dest_start + i] = chr(ord(dest[dest_start + i]) ^ ord(source[source_start + i]))

    def pbkdf2(passphrase, salt, count, dkLen, prf):

        def f(block_number):

            U = prf(passphrase, salt + struct.pack('>L', block_number))

            if count > 1:
                U = [c for c in U]
                for _ in range(2, 1 + count):
                    blockxor(prf(passphrase, ''.join(U)), 0, U, 0, len(U))
                U = ''.join(U)

            return U

        size = 0

        block_number = 0
        blocks = []

        while size < dkLen:
            block_number += 1
            block = f(block_number)

            blocks.append(block)
            size += len(block)

        return b''.join(blocks)[:dkLen]

    def integerify(B, Bi, r):

        Bi += (2 * r - 1) * 64
        n = B[Bi] | (B[Bi + 1] << 8) | (B[Bi + 2] << 16) | (B[Bi + 3] << 24)
        return n

    def make_int32(v):

        if v > 0x7fffffff:
            return -1 * ((~v & 0xffffffff) + 1)
        return v

    def R(X, destination, a1, a2, b):

        a = (X[a1] + X[a2]) & 0xffffffff
        X[destination] ^= ((a << b) | (a >> (32 - b)))

    def salsa20_8(B):

        B32 = [make_int32((B[i * 4] | (B[i * 4 + 1] << 8) | (B[i * 4 + 2] << 16) | (B[i * 4 + 3] << 24))) for i in range(16)]
        x = [i for i in B32]

        for _ in range(8, 0, -2):
            R(x, 4, 0, 12, 7); R(x, 8, 4, 0, 9); R(x, 12, 8, 4, 13); R(x, 0, 12, 8, 18)
            R(x, 9, 5, 1, 7); R(x, 13, 9, 5, 9); R(x, 1, 13, 9, 13); R(x, 5, 1, 13, 18)
            R(x, 14, 10, 6, 7); R(x, 2, 14, 10, 9); R(x, 6, 2, 14, 13); R(x, 10, 6, 2, 18)
            R(x, 3, 15, 11, 7); R(x, 7, 3, 15, 9); R(x, 11, 7, 3, 13); R(x, 15, 11, 7, 18)
            R(x, 1, 0, 3, 7); R(x, 2, 1, 0, 9); R(x, 3, 2, 1, 13); R(x, 0, 3, 2, 18)
            R(x, 6, 5, 4, 7); R(x, 7, 6, 5, 9); R(x, 4, 7, 6, 13); R(x, 5, 4, 7, 18)
            R(x, 11, 10, 9, 7); R(x, 8, 11, 10, 9); R(x, 9, 8, 11, 13); R(x, 10, 9, 8, 18)
            R(x, 12, 15, 14, 7); R(x, 13, 12, 15, 9); R(x, 14, 13, 12, 13); R(x, 15, 14, 13, 18)

        B32 = [make_int32(x[i] + B32[i]) for i in range(16)]

        for i in range(16):
            B[i * 4 + 0] = (B32[i] >> 0) & 0xff
            B[i * 4 + 1] = (B32[i] >> 8) & 0xff
            B[i * 4 + 2] = (B32[i] >> 16) & 0xff
            B[i * 4 + 3] = (B32[i] >> 24) & 0xff

    def blockmix_salsa8(BY, Bi, Yi, r):

        start = Bi + (2 * r - 1) * 64
        X = [BY[i] for i in range(start, start + 64)]  

        for i in range(2 * r):  
            blockxor(BY, i * 64, X, 0, 64)  
            salsa20_8(X)  
            array_overwrite(X, 0, BY, Yi + (i * 64), 64)  

        for i in range(r):  
            array_overwrite(BY, Yi + (i * 2) * 64, BY, Bi + (i * 64), 64)

        for i in range(r):
            array_overwrite(BY, Yi + (i * 2 + 1) * 64, BY, Bi + (i + r) * 64, 64)

    def smix(B, Bi, r, N, V, X):

        array_overwrite(B, Bi, X, 0, 128 * r)  

        for i in range(N):  
            array_overwrite(X, 0, V, i * (128 * r), 128 * r)  
            blockmix_salsa8(X, 0, 128 * r, r)  

        for i in range(N):  
            j = integerify(X, 0, r) & (N - 1)  
            blockxor(V, j * (128 * r), X, 0, 128 * r)  
            blockmix_salsa8(X, 0, 128 * r, r)  

        array_overwrite(X, 0, B, Bi, 128 * r)  

    if N < 2 or (N & (N - 1)):
        raise ValueError('Scrypt N must be a power of 2 greater than 1')

    prf = lambda k, m: hmac.new(key=k, msg=m, digestmod=hashlib.sha256).digest()

    DK = [chr(0)] * dkLen

    B = [c for c in pbkdf2(password, salt, 1, p * 128 * r, prf)]
    XY = [chr(0)] * (256 * r)
    V = [chr(0)] * (128 * r * N)

    for i in range(p):
        smix(B, i * 128 * r, r, N, V, XY)

    return pbkdf2(password, ''.join(B), 1, dkLen, prf)

SCRYPT_LIBRARY = None
scrypt_proof_of_work = None

def set_scrypt_library(library=SCRYPT_LIBRARY_AUTO):

    global SCRYPT_LIBRARY
    global scrypt_proof_of_work

    if library == SCRYPT_LIBRARY_LTC:
        import ltc_scrypt
        scrypt_proof_of_work = ltc_scrypt.getPoWHash
        SCRYPT_LIBRARY = library

    elif library == SCRYPT_LIBRARY_SCRYPT:
        import scrypt as NativeScrypt
        scrypt_proof_of_work = lambda header: NativeScrypt.hash(header, header, 1024, 1, 1, 32)
        SCRYPT_LIBRARY = library

    elif library == SCRYPT_LIBRARY_AUTO:
        try:
            set_scrypt_library(SCRYPT_LIBRARY_LTC)
        except Exception as e:
            try:
                set_scrypt_library(SCRYPT_LIBRARY_SCRYPT)
            except Exception as e:
                set_scrypt_library(SCRYPT_LIBRARY_PYTHON)

    else:
        scrypt_proof_of_work = lambda header: scrypt(header, header, 1024, 1, 1, 32)
        SCRYPT_LIBRARY = library

set_scrypt_library()

class Job(object):

    def __init__(self, job_id, prevhash, coinb1, coinb2, merkle_branches, version, nbits, ntime, target, extranounce1, extranounce2_size, proof_of_work):

        self._job_id = job_id
        self._prevhash = prevhash
        self._coinb1 = coinb1
        self._coinb2 = coinb2
        self._merkle_branches = [b for b in merkle_branches]
        self._version = version
        self._nbits = nbits
        self._ntime = ntime

        self._target = target
        self._extranounce1 = extranounce1
        self._extranounce2_size = extranounce2_size

        self._proof_of_work = proof_of_work

        self._done = False

        self._dt = 0.0
        self._hash_count = 0

    id = property(lambda s: s._job_id)
    prevhash = property(lambda s: s._prevhash)
    coinb1 = property(lambda s: s._coinb1)
    coinb2 = property(lambda s: s._coinb2)
    merkle_branches = property(lambda s: [b for b in s._merkle_branches])
    version = property(lambda s: s._version)
    nbits = property(lambda s: s._nbits)
    ntime = property(lambda s: s._ntime)

    target = property(lambda s: s._target)
    extranounce1 = property(lambda s: s._extranounce1)
    extranounce2_size = property(lambda s: s._extranounce2_size)

    proof_of_work = property(lambda s: s._proof_of_work)

    @property
    def hashrate(self):

        if self._dt == 0:
            return 0.0
        return self._hash_count / self._dt

    def merkle_root_bin(self, extranounce2_bin):

        coinbase_bin = unhexlify(self._coinb1) + unhexlify(self._extranounce1) + extranounce2_bin + unhexlify(self._coinb2)
        coinbase_hash_bin = sha256d(coinbase_bin)

        merkle_root = coinbase_hash_bin
        for branch in self._merkle_branches:
            merkle_root = sha256d(merkle_root + unhexlify(branch))
        return merkle_root

    def stop(self):

        self._done = True

    def mine(self, nounce_start=0, nounce_stride=1):

        t0 = time.time()

        for extranounce2 in range(0, 0x7fffffff):
            extranounce2_bin = struct.pack('<I', extranounce2)

            merkle_root_bin = self.merkle_root_bin(extranounce2_bin)
            header_prefix_bin = swap_endian_word(self._version) + swap_endian_words(self._prevhash) + merkle_root_bin + swap_endian_word(self._ntime) + swap_endian_word(self._nbits)
            for nounce in range(nounce_start, 0x7fffffff, nounce_stride):
                if self._done:
                    self._dt += (time.time() - t0)
                    raise StopIteration()

                nounce_bin = struct.pack('<I', nounce)
                pow = self.proof_of_work(header_prefix_bin + nounce_bin)[::-1].hex()

                if pow <= self.target:
                    result = dict(
                        job_id=self.id,
                        extranounce2=hexlify(extranounce2_bin),
                        ntime=str(self._ntime),
                        nounce=hexlify(nounce_bin[::-1])
                    )
                    self._dt += (time.time() - t0)
                    yield result
                    t0 = time.time()

                self._hash_count += 1

    def __str__(self):
        return '<Job id=%s prevhash=%s coinb1=%s coinb2=%s merkle_branches=%s version=%s nbits=%s ntime=%s target=%s extranounce1=%s extranounce2_size=%d>' % (
            self.id, self.prevhash, self.coinb1, self.coinb2, self.merkle_branches, self.version, self.nbits, self.ntime, self.target, self.extranounce1, self.extranounce2_size)

class Subscription(object):

    def ProofOfWork(header):
        raise Exception('Do not use the Subscription class directly, subclass it')

    class StateException(Exception):
        pass

    def __init__(self):
        self._id = None
        self._difficulty = None
        self._extranounce1 = None
        self._extranounce2_size = None
        self._target = None
        self._worker_name = None

        self._mining_thread = None

    id = property(lambda s: s._id)
    worker_name = property(lambda s: s._worker_name)

    difficulty = property(lambda s: s._difficulty)
    target = property(lambda s: s._target)

    extranounce1 = property(lambda s: s._extranounce1)
    extranounce2_size = property(lambda s: s._extranounce2_size)

    def set_worker_name(self, worker_name):
        if self._worker_name:
            raise self.StateException('Already authenticated as %r (requesting %r)' % (self._worker_name, worker_name))

        self._worker_name = worker_name

    def _set_target(self, target):
        self._target = '%064x' % target

    def set_difficulty(self, difficulty):
        if difficulty < 0:
            raise self.StateException('Difficulty must be non-negative')

        if difficulty == 0:
            target = 2 ** 256 - 1
        else:
            target = min(int((0xffff0000 * 2 ** (256 - 64) + 1) / difficulty - 1 + 0.5), 2 ** 256 - 1)

        self._difficulty = difficulty
        self._set_target(target)

    def set_subscription(self, subscription_id, extranounce1, extranounce2_size):
        if self._id is not None:
            raise self.StateException('Already subscribed')

        self._id = subscription_id
        self._extranounce1 = extranounce1
        self._extranounce2_size = extranounce2_size

    def create_job(self, job_id, prevhash, coinb1, coinb2, merkle_branches, version, nbits, ntime):

        if self._id is None:
            raise self.StateException('Not subscribed')

        return Job(
            job_id=job_id,
            prevhash=prevhash,
            coinb1=coinb1,
            coinb2=coinb2,
            merkle_branches=merkle_branches,
            version=version,
            nbits=nbits,
            ntime=ntime,
            target=self.target,
            extranounce1=self._extranounce1,
            extranounce2_size=self.extranounce2_size,
            proof_of_work=self.ProofOfWork
        )

    def __str__(self):
        return '<Subscription id=%s, extranounce1=%s, extranounce2_size=%d, difficulty=%d worker_name=%s>' % (self.id, self.extranounce1, self.extranounce2_size, self.difficulty, self.worker_name)

class SubscriptionScrypt(Subscription):

    ProofOfWork = lambda s, h: (scrypt_proof_of_work(h))

    def _set_target(self, target):
        self._target = '%064x' % (target << 16)

class SubscriptionSHA256D(Subscription):

    ProofOfWork = sha256d

SubscriptionByAlgorithm = {ALGORITHM_SCRYPT: SubscriptionScrypt, ALGORITHM_SHA256D: SubscriptionSHA256D}

class SimpleJsonRpcClient(object):

    class ClientException(Exception):
        pass

    class RequestReplyException(Exception):
        def __init__(self, message, reply, request=None):
            super().__init__(message)
            self._reply = reply
            self._request = request

        request = property(lambda s: s._request)
        reply = property(lambda s: s._reply)

    class RequestReplyWarning(RequestReplyException):

        pass

    def __init__(self):
        self._socket = None
        self._lock = threading.RLock()
        self._rpc_thread = None
        self._message_id = 1
        self._requests = dict()

    def _handle_incoming_rpc(self):
        data = ""
        while True:
            if '\n' in data:
                (line, data) = data.split('\n', 1)
            else:
                chunk = self._socket.recv(1024).decode()
                data += chunk
                continue

            log('JSON-RPC Server > ' + line, LEVEL_PROTOCOL)

            try:
                reply = json.loads(line)
            except Exception as e:
                log(f"JSON-RPC Error: Failed to parse JSON {line!r} (skipping)", LEVEL_ERROR)
                continue

            try:
                request = None
                with self._lock:
                    if 'id' in reply and reply['id'] in self._requests:
                        request = self._requests[reply['id']]
                    self.handle_reply(request=request, reply=reply)
            except self.RequestReplyWarning as e:
                output = e.message
                if e.request:
                    output += '\n  ' + e.request
                output += '\n  ' + e.reply
                log(output, LEVEL_ERROR)

    def handle_reply(self, request, reply):
        raise self.RequestReplyWarning('Override this method')

    def send(self, method, params):

        if not self._socket:
            raise self.ClientException('Not connected')

        request = dict(id=self._message_id, method=method, params=params)
        message = json.dumps(request)
        with self._lock:
            self._requests[self._message_id] = request
            self._message_id += 1
            self._socket.send((message + '\n').encode())

        log('JSON-RPC Server < ' + message, LEVEL_PROTOCOL)
        return request

    def connect(self, socket):

        if self._rpc_thread:
            raise self.ClientException('Already connected')

        self._socket = socket
        self._rpc_thread = threading.Thread(target=self._handle_incoming_rpc)
        self._rpc_thread.daemon = True
        self._rpc_thread.start()

class Miner(SimpleJsonRpcClient):

    class MinerWarning(SimpleJsonRpcClient.RequestReplyWarning):
        def __init__(self, message, reply, request=None):
            super().__init__('Mining State Error: ' + message, reply, request)

    class MinerAuthenticationException(SimpleJsonRpcClient.RequestReplyException):
        pass

    def __init__(self, url, username, password, algorithm=ALGORITHM_SCRYPT):
        super().__init__()
        self._url = url
        self._username = username
        self._password = password
        self._subscription = SubscriptionByAlgorithm[algorithm]()
        self._job = None
        self._accepted_shares = 0

    url = property(lambda s: s._url)
    username = property(lambda s: s._username)
    password = property(lambda s: s._password)

    def handle_reply(self, request, reply):
        if reply.get('method') == 'mining.notify':
            if 'params' not in reply or len(reply['params']) != 9:
                raise self.MinerWarning('Malformed mining.notify message', reply)

            (job_id, prevhash, coinb1, coinb2, merkle_branches, version, nbits, ntime, clean_jobs) = reply['params']
            self._spawn_job_thread(job_id, prevhash, coinb1, coinb2, merkle_branches, version, nbits, ntime)
            log('New job: job_id=%s' % job_id, LEVEL_DEBUG)

        elif reply.get('method') == 'mining.set_difficulty':
            if 'params' not in reply or len(reply['params']) != 1:
                raise self.MinerWarning('Malformed mining.set_difficulty message', reply)

            (difficulty,) = reply['params']
            self._subscription.set_difficulty(difficulty)
            log('Change difficulty: difficulty=%s' % difficulty, LEVEL_DEBUG)

        elif request:
            if request.get('method') == 'mining.subscribe':
                if 'result' not in reply or len(reply['result']) != 3 or len(reply['result'][0]) != 2:
                    raise self.MinerWarning('Reply to mining.subscribe is malformed', reply, request)

                ((mining_notify, subscription_id), extranounce1, extranounce2_size) = reply['result']
                self._subscription.set_subscription(subscription_id, extranounce1, extranounce2_size)
                log('Subscribed: subscription_id=%s' % subscription_id, LEVEL_DEBUG)
                self.send(method='mining.authorize', params=[self.username, self.password])

            elif request.get('method') == 'mining.authorize':
                if 'result' not in reply or not reply['result']:
                    raise self.MinerAuthenticationException('Failed to authenticate worker', reply, request)

                worker_name = request['params'][0]
                self._subscription.set_worker_name(worker_name)
                log('Authorized: worker_name=%s' % worker_name, LEVEL_DEBUG)

            elif request.get('method') == 'mining.submit':
                if 'result' not in reply or not reply['result']:
                    log('Share - Invalid', LEVEL_INFO)
                    raise self.MinerWarning('Failed to accept submit', reply, request)

                self._accepted_shares += 1
                log('Accepted shares: %d' % self._accepted_shares, LEVEL_INFO)

            else:
                raise self.MinerWarning('Unhandled message', reply, request)

        else:
            raise self.MinerWarning('Bad message state', reply)

    def _spawn_job_thread(self, job_id, prevhash, coinb1, coinb2, merkle_branches, version, nbits, ntime):

        if self._job:
            self._job.stop()

        self._job = self._subscription.create_job(
            job_id=job_id,
            prevhash=prevhash,
            coinb1=coinb1,
            coinb2=coinb2,
            merkle_branches=merkle_branches,
            version=version,
            nbits=nbits,
            ntime=ntime
        )

        def run(job):
            try:
                for result in job.mine():
                    params = [self._subscription.worker_name] + [result[k] for k in ('job_id', 'extranounce2', 'ntime', 'nounce')]
                    self.send(method='mining.submit', params=params)
                    log("Found share: " + str(params), LEVEL_INFO)
                log("Hashrate: %s" % human_readable_hashrate(job.hashrate), LEVEL_INFO)
            except Exception as e:
                log(f"ERROR: {e}", LEVEL_ERROR)

        thread = threading.Thread(target=run, args=(self._job,))
        thread.daemon = True
        thread.start()

    def serve_forever(self):

        url = urlparse(self.url)
        hostname = url.hostname or ''
        port = url.port or 9333

        log(f'Starting server on {hostname}:{port}', LEVEL_INFO)
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.connect((hostname, port))
        self.connect(sock)
        self.send(method='mining.subscribe', params=[f"{USER_AGENT}/{'.'.join(str(p) for p in VERSION)}"])

        while True:
            time.sleep(10)

def test_subscription():

    log(f'TEST: Scrypt algorithm = {SCRYPT_LIBRARY!r}', LEVEL_DEBUG)
    log('TEST: Testing Subscription', LEVEL_DEBUG)

    subscription = SubscriptionScrypt()
    reply = json.loads('{"error": null, "id": 1, "result": [["mining.notify", "ae6812eb4cd7735a302a8a9dd95cf71f"], "f800880e", 4]}')
    log(f'TEST: {reply!r}', LEVEL_DEBUG)
    ((mining_notify, subscription_id), extranounce1, extranounce2_size) = reply['result']
    subscription.set_subscription(subscription_id, extranounce1, extranounce2_size)

    reply = json.loads('{"params": [32], "id": null, "method": "mining.set_difficulty"}')
    log(f'TEST: {reply!r}', LEVEL_DEBUG)
    (difficulty,) = reply['params']
    subscription.set_difficulty(difficulty)

    reply = json.loads('{"params": ["1db7", "0b29bfff96c5dc08ee65e63d7b7bab431745b089ff0cf95b49a1631e1d2f9f31", "01000000010000000000000000000000000000000000000000000000000000000000000000ffffffff2503777d07062f503253482f0405b8c75208", "0b2f436f696e48756e74722f0000000001603f352a010000001976a914c633315d376c20a973a758f7422d67f7bfed9c5888ac00000000", ["f0dbca1ee1a9f6388d07d97c1ab0de0e41acdf2edac4b95780ba0a1ec14103b3", "8e43fd2988ac40c5d97702b7e5ccdf5b06d58f0e0d323f74dd5082232c1aedf7", "1177601320ac928b8c145d771dae78a3901a089fa4aca8def01cbff747355818", "9f64f3b0d9edddb14be6f71c3ac2e80455916e207ffc003316c6a515452aa7b4", "2d0b54af60fad4ae59ec02031f661d026f2bb95e2eeb1e6657a35036c017c595"], "00000002", "1b148272", "52c7b81a", true], "id": null, "method": "mining.notify"}')
    log(f'TEST: {reply!r}', LEVEL_DEBUG)
    (job_id, prevhash, coinb1, coinb2, merkle_branches, version, nbits, ntime, clean_jobs) = reply['params']
    job = subscription.create_job(
        job_id=job_id,
        prevhash=prevhash,
        coinb1=coinb1,
        coinb2=coinb2,
        merkle_branches=merkle_branches,
        version=version,
        nbits=nbits,
        ntime=ntime
    )

    for result in job.mine(nounce_start=1210450368 - 3):
        log(f'TEST: found share - {result!r}', LEVEL_DEBUG)
        break

    valid = {'ntime': '52c7b81a', 'nounce': '482601c0', 'extranounce2': '00000000', 'job_id': '1db7'}
    log(f'TEST: Correct answer {valid!r}', LEVEL_DEBUG)

if __name__ == '__main__':
    import argparse

    parser = argparse.ArgumentParser(description="CPU-Miner for Cryptocurrency using the stratum protocol")
    parser.add_argument('-o', '--url', help='stratum mining server url (eg: stratum+tcp://foobar.com:3333)')
    parser.add_argument('-u', '--user', dest='username', default='', help='username for mining server', metavar="USERNAME")
    parser.add_argument('-p', '--pass', dest='password', default='', help='password for mining server', metavar="PASSWORD")
    parser.add_argument('-O', '--userpass', help='username:password pair for mining server', metavar="USERNAME:PASSWORD")
    parser.add_argument('-a', '--algo', default=ALGORITHM_SCRYPT, choices=ALGORITHMS, help='hashing algorithm to use for proof of work')
    parser.add_argument('-B', '--background', action='store_true', help='run in the background as a daemon')
    parser.add_argument('-q', '--quiet', action='store_true', help='suppress non-errors')
    parser.add_argument('-P', '--dump-protocol', dest='protocol', action='store_true', help='show all JSON-RPC chatter')
    parser.add_argument('-d', '--debug', action='store_true', help='show extra debug information')
    parser.add_argument('-v', '--version', action='version', version=f'{USER_AGENT}/{". ".join(str(v) for v in VERSION)}')

    options = parser.parse_args(sys.argv[1:])
    message = None

    username = options.username
    password = options.password

    if options.userpass:
        if username or password:
            message = 'May not use -O/-userpass in conjunction with -u/--user or -p/--pass'
        else:
            try:
                username, password = options.userpass.split(':')
            except Exception:
                message = 'Could not parse username:password for -O/--userpass'

    if message:
        parser.print_help()
        print("\n", message)
        sys.exit(1)

    if options.debug:
        DEBUG = True
    if options.protocol:
        DEBUG_PROTOCOL = True
    if options.quiet:
        QUIET = True

    if DEBUG:
        for library in SCRYPT_LIBRARIES:
            set_scrypt_library(library)
            test_subscription()

        set_scrypt_library()
        if options.algo == ALGORITHM_SCRYPT:
            log(f'Using scrypt library {SCRYPT_LIBRARY!r}', LEVEL_DEBUG)

    if options.background:
        import os
        if os.fork() or os.fork():
            sys.exit()

    if options.url:
        miner = Miner(options.url, username, password, algorithm=options.algo)
        miner.serve_forever()