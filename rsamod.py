"""
Encryption/Decryption toolkit
Contains RSA and AES tools
"""

from binascii import hexlify as hexl, unhexlify as unhexl
import hashlib
import base64
import random
import re
import math
from fractions import gcd
from Crypto.Cipher import AES
import time, datetime
import getpass
secure_random = random.SystemRandom()
version = "0.04"

class RSA_public_key():
    def __init__(self, n, e):
        self.n = n
        self.e = e

class RSA_private_key():
    def __init__(self, n, d, p=None, q=None, invq=None):
        self.n = n
        self.d = d
        self.p = p
        self.q = q
        self.dp = d % (p - 1)
        self.dq = d % (q - 1)
        self.invq = invq

def to_bytes_prepended(m, prependedbytesize=4):
    if type(m) == list:
        mstring = b""
        for message in m:
            mstring+=to_bytes_prepended(message, prependedbytesize)
        return(mstring)
    if type(m) == int: m = b"\x00"+I2OSP(m,0)
    mLen = len(m)
    return(I2OSP(mLen, prependedbytesize)+m)

def to_bytes_prepended_LV(m, prependedbytesize=4):
    m = m.encode()
    m = to_bytes_prepended(m, prependedbytesize)
    l = []
    for i in m:
        l.append(int(i))
    
    return(l)

def from_bytes_prepended(b, prependedbytesize=4):
    position = 0
    messages = []
    while position < len(b):
        mLen = b[position:position+prependedbytesize]
        ImLen = OS2IP(mLen)
        position += prependedbytesize
        m = b[position:position+ImLen]
        position += ImLen
        messages.append(m)
    return(messages)


def _try_composite(a, d, n, s):
    if pow(a, d, n) == 1:
        return False
    for i in range(s):
        if pow(a, 2**i * d, n) == n-1:
            return False
    return True

def _is_prime(n, _precision_for_huge_n=16):
    if n in _known_primes or n in (0, 1):
        return True
    if any((n % p) == 0 for p in _known_primes):
        return False
    d, s = n - 1, 0
    while not d % 2:
        d, s = d >> 1, s + 1
    if n < 1373653: 
        return not any(_try_composite(a, d, n, s) for a in (2, 3))
    if n < 25326001: 
        return not any(_try_composite(a, d, n, s) for a in (2, 3, 5))
    if n < 118670087467: 
        if n == 3215031751: 
            return False
        return not any(_try_composite(a, d, n, s) for a in (2, 3, 5, 7))
    if n < 2152302898747: 
        return not any(_try_composite(a, d, n, s) for a in (2, 3, 5, 7, 11))
    if n < 3474749660383: 
        return not any(_try_composite(a, d, n, s) for a in (2, 3, 5, 7, 11, 13))
    if n < 341550071728321: 
        return not any(_try_composite(a, d, n, s) for a in (2, 3, 5, 7, 11, 13, 17))
    return not any(_try_composite(a, d, n, s) 
                   for a in _known_primes[:_precision_for_huge_n])

_known_primes = [2, 3]
_known_primes += [x for x in range(5, 20000, 2) if _is_prime(x)]

def _carmichael(n):
    coprimes = [x for x in range(1, n) if gcd(x, n) == 1]
    k = 1
    while not all(pow(x, k, n) == 1 for x in coprimes):
        k += 1
    return k

def _lcm(x, y):
    return((x*y)//gcd(x,y))

def _egcd(a, b):
    if a == 0:
        return(b, 0, 1)
    else:
        g, y, x = _egcd(b % a, a)
        return (g, x- (b // a) * y, y)

def _modinv(a, m):
    g, x, y = _egcd(a, m)
    if g != 1:
        raise Exception('modular inverse does not exist')
    else:
        return(x % m)

def _get_two_primes(size):
    done = False
    p = secure_random.randint(pow(2, size-1),pow(2, size))
    q = secure_random.randint(pow(2, size-1),pow(2, size))
    p += 3
    q += 3
    p_done = False
    q_done = False
    while not done:
        if not p_done:
            p_done = _is_prime(p)
            if not p_done: p += 1
        if not q_done:
            q_done = _is_prime(q)
            if not q_done: q += 1
        if p_done and q_done: done = True
    return(p, q)

def _get_prime(size):
    done = False
    p = secure_random.randint(pow(2, size-1),pow(2, size))
    p += 3
    while not done:
        done = _is_prime(p)
        if not done: p += 1
    return(p)
    
def _get_n(p, q):
    n = p*q
    return(n)

def _get_carmichaels(p, q):
    c = _lcm(p-1,q-1)
    return(c)

def _get_e(c):
    g = []
    for prime in _known_primes:
        if gcd(prime, c) == 1:
            g.append(prime)
        if prime > c or len(g) > 20:
            break
    e = secure_random.choice(g)
    return(e)

def _get_modinv(e, c):
    d = _modinv(e, c)
    return(d)

def _decode_key_info(s,typ):
    num_buff = ""
    s = base64.b64decode(s)
    finding_length = True
    length = 0
    step = 0
    message = 0 if typ == "pub" else 3
    messages = []
    for b in s:
        if finding_length:
            num_buff += hex(b)[2:].zfill(2)
            if len(num_buff) == 8:
                length = int(num_buff,16)
                finding_length = False
                step = 0
                num_buff = ""
        else:
            if step < length:
                num_buff += hex(b)[2:].zfill(2)
                step += 1
            if step == length:
                finding_length = True
                if message == 0: #Keytype
                    _m = ""
                    for i in range(len(num_buff)//2):
                        _m += chr(int(num_buff[i*2]+num_buff[i*2+1],16))
                    messages.append("{}".format(_m))
                elif message == 1: #Exponent
                    messages.append("{}".format(int(num_buff,16)))
                elif message == 2: #Modulus
                    messages.append("{}".format(int(num_buff,16)))
                elif message == 3: #D
                    messages.append("{}".format(int(num_buff,16)))
                elif message == 4: #P
                    messages.append("{}".format(int(num_buff,16)))
                elif message == 5: #Q
                    messages.append("{}".format(int(num_buff,16)))
                elif message == 6: #InvQ
                    messages.append("{}".format(int(num_buff,16)))
                else:
                    messages.append(int(num_buff,16))
                message += 1
                num_buff = ""
    if typ == "pub":
        return({"KeyType":messages[0],
                "Exponent":messages[1],
                "Modulus":messages[2]})
    else:
        return({"d":messages[0],
                "p":messages[1],
                "q":messages[2],
                "invq":messages[3]})

def _vigenere_m(m, key, reverse=False):
    padded_key = (key*((len(m)//len(key))+1))[:len(m)]
    if not reverse:
        output = b"".join(bytes([(m[i]+padded_key[i])%256]) for i in range(len(m)))
    else:
        output = b"".join(bytes([(m[i]-padded_key[i])%256]) for i in range(len(m)))
    return(output)

def _get_hex(m):
    m = '0'*(len(hex(m)[2:])%2)+hex(m)[2:]
    #print("m: {}".format(len(m)))
    if not 4-len(m)%4 == 2: m = "00"+m
    m = '0'*(8-(len(hex(len(m)//2)[2:])%8))+hex(len(m)//2)[2:]+''+m
    return(m)

def I2OSP(x, xLen):
    if xLen == 0: xLen = math.ceil(x.bit_length()/8)
    if x >= pow(256, xLen): raise ValueError("integer too large")
    h=hex(x)[2:].zfill(xLen*2)
    if len(h)&1: h="0"+h
    h = unhexl(h)
    return(h)
    
def I2OSP_LV(x, xLen):
    y = []
    for i in I2OSP(x, xLen):
        y.append(i)
    return(y)

def OS2IP(x):
    return(int(hexl(x),16) if x else 0)
    
def OS2IP_LV(x):
    m = bytes(x)
    return(OS2IP(m))
    
def RSAEP(public_key, m):
    n, e = (public_key.n, public_key.e)
    if not m > 0 or not m < n - 1: raise ValueError("message representative out of range")
    return(pow(m, e, n))

def RSADP(private_key, c):
    n, d = (private_key.n, private_key.d)
    if not c > 0 and not c < n - 1: raise ValueError("ciphertext representative out of range")
    return(pow(c, d, n))

def RSADP_opt(private_key, c):
    m1 = pow(c, private_key.dp, private_key.p)
    m2 = pow(c, private_key.dq, private_key.q)
    h = (private_key.invq*(m1-m2)) % private_key.p
    return(m2+h*private_key.q)

def RSASP1(private_key, m):
    n, d = (private_key.n, private_key.d)
    if not m > 0 and not m < n - 1: raise ValueError("message representative out of range")
    return(pow(m, d, n))

def RSAVP1(public_key, s):
    n, e = (public_key.n, public_key.e)
    if not s > 0 and not s < n - 1: raise ValueError("signature representative out of range")
    return(pow(s, e, n))

def mgf1(input, length, hash=hashlib.sha1):
    counter = 0
    output = b''
    while (len(output) < length):
        C = I2OSP(counter, 4)
        output += hash((input + C)).digest()
        counter += 1
    return(I2OSP(int(hexl(output[:length]),16),length))

def hmac(key, message, h=hashlib.sha1, blockSize=64):
    if len(key) > blockSize:
        key = h(key).digest()

    if len(key) < blockSize:
        key = key + b"\x00"*(blockSize-len(key))

    o_key_pad = I2OSP(OS2IP(key) ^ OS2IP(b"\x5c"*blockSize), blockSize)
    i_key_pad = I2OSP(OS2IP(key) ^ OS2IP(b"\x36"*blockSize), blockSize)

    return(h(o_key_pad+h(i_key_pad+message).digest()).digest())

def RSAES_OAEP_ENCRYPT(public_key, M, L=b"", Hash=hashlib.sha1, MGF=mgf1):
    n, e = (public_key.n, public_key.e)
    hLen = len(Hash(b"").digest())
    k = (len(hex(n)[2:])+(len(hex(n)[2:])%2))//2
    mLen = len(M)
    if len(L) > pow(2, 61) - 1: raise ValueError("label too long")
    if mLen > k - 2*hLen - 2: raise ValueError("message too long")
    lHash = Hash(L).digest()
    PS = b"".join(b"\x00" for i in range(k - mLen - 2*hLen - 2))
    DB = lHash + PS + b"\x01" + M
    seed = bytes([secure_random.getrandbits(8) for i in range(hLen)])
    dbMask = MGF(seed, k - hLen - 1)
    maskedDB = I2OSP(OS2IP(DB) ^ OS2IP(dbMask), k - hLen - 1)
    seedMask = MGF(maskedDB, hLen)
    maskedSeed = I2OSP(OS2IP(seed) ^ OS2IP(seedMask), hLen)
    EM = b"\x00" + maskedSeed + maskedDB
    m = OS2IP(EM)
    c = RSAEP(public_key, m)
    C = I2OSP(c, k)
    return(C)

def RSAES_OAEP_DECRYPT(private_key, C, L=b"", Hash=hashlib.sha1, MGF=mgf1):
    n, d = (private_key.n, private_key.d)
    hLen = len(Hash(b"").digest())
    k = (len(hex(n)[2:])+(len(hex(n)[2:])%2))//2
    if len(L) > pow(2, 61) - 1: raise ValueError("label too long")
    if not len(C) == k: raise Exception("decryption error")
    if k < 2*hLen + 2: raise Exception("decryption error")
    c = OS2IP(C)
    m = RSADP_opt(private_key, c)
    EM = I2OSP(m, k)
    lHash = Hash(L).digest()
    Y = EM[0]
    maskedSeed = EM[1:1+hLen]
    maskedDB = EM[1+hLen:2+hLen + k - hLen - 1]
    seedMask = MGF(maskedDB, hLen)
    seed = I2OSP(OS2IP(maskedSeed) ^ OS2IP(seedMask), hLen)
    dbMask = MGF(seed, k - hLen - 1)
    DB = I2OSP(OS2IP(maskedDB) ^ OS2IP(dbMask), k - hLen - 1)
    lHash2 = DB[:hLen]
    counter = 0
    while True:
        if not DB[hLen+counter] == 0:
            counter = hLen+counter
            break
        counter += 1
    one = DB[counter]
    M = DB[counter+1:]
    if not one == 1: raise Exception("decryption error")
    if not lHash == lHash2: raise Exception("decryption error")
    if not Y == 0: raise Exception("decryption error")
    return(M)

def RSAES_PKCS1_V1_5_ENCRYPT(public_key, M):
    n, e = (public_key.n, public_key.e)
    k = (len(hex(n)[2:])+(len(hex(n)[2:])%2))//2
    mLen = len(M)
    if mLen > k - 11: raise ValueError("message too long")
    PS = bytes([secure_random.randint(1, 255) for i in range(k - mLen - 3)])
    EM = b"\x00" + b"\x02" + PS + b"\x00" + M
    m = OS2IP(EM)
    c = RSAEP(public_key, m)
    C = I2OSP(c, k)
    return(C)

def RSAES_PKCS1_V1_5_DECRYPT(private_key, C):
    n, d = (private_key.n, private_key.d)
    k = (len(hex(n)[2:])+(len(hex(n)[2:])%2))//2
    if not len(C) == k or k < 11: raise Exception("decryption error")
    c = OS2IP(C)
    m = RSADP_opt(private_key, c)
    EM = I2OSP(m, k)
    zero1 = EM[0]
    two = EM[1]
    counter = 0
    PS = b""
    while True:
        if EM[2+counter] == 0:
            counter = 2+counter
            break
        PS += bytes([EM[2+counter]])
        counter += 1
    zero2 = EM[counter]
    M = EM[counter+1:]
    if not zero1 == 0: raise Exception("decryption error")
    if not two == 2: raise Exception("decryption error")
    if not zero2 == 0: raise Exception("decryption error")
    if len(PS) < 8: raise Exception("decryption error")
    return(M)

def EMSA_PSS_ENCODE(M, emBits, Hash=hashlib.sha1, MGF=mgf1, sLen=0):
    hLen = len(Hash(b"").digest())
    emLen = math.ceil(emBits/8)
    if len(M) > pow(2, 61) - 1: raise ValueError("message too long")
    mHash = Hash(M).digest()
    if emLen < hLen + sLen + 2: raise Exception("encoding error")
    salt = b"" if sLen == 0 else bytes([secure_random.getrandbits(8) for i in range(sLen)])
    M2 = b"\x00"*8 + mHash + salt
    H = Hash(M2).digest()
    PS = b"\x00"*(emLen - sLen - hLen - 2)
    DB = PS + b"\x01" + salt
    dbMask = MGF(H, emLen - hLen - 1)
    maskedDB = I2OSP(OS2IP(DB) ^ OS2IP(dbMask), emLen - hLen - 1)
    maskedDB = bytes([int("0"*(8*emLen - emBits)+bin(maskedDB[0])[2:].zfill(8)[8*emLen - emBits:],2)])+maskedDB[1:]
    EM = maskedDB + H + b"\xbc"
    return(EM)

def EMSA_PSS_VERIFY(M, EM, emBits, Hash=hashlib.sha1, MGF=mgf1, sLen=0):
    hLen = len(Hash(b"").digest())
    emLen = math.ceil(emBits/8)
    if len(M) > pow(2, 61) - 1: return("inconsistent")
    mHash = Hash(M).digest()
    if emLen < hLen + sLen + 2: return("inconsistent")
    if not EM[-1] == 188: return("inconsistent")
    maskedDB = EM[:emLen - hLen  - 1]
    H = EM[emLen - hLen - 1:emLen - 1]
    if not int(bin(maskedDB[0])[2:].zfill(8)[:8*emLen - emBits],2) == 0: return("inconsistent")
    dbMask = MGF(H, emLen - hLen - 1)
    DB = I2OSP(OS2IP(maskedDB) ^ OS2IP(dbMask), emLen - hLen - 1)
    DB = bytes([int("0"*(8*emLen - emBits)+bin(DB[0])[2:].zfill(8)[8*emLen - emBits:],2)])+DB[1:]
    for bit in DB[:emLen - hLen - sLen - 2]:
        if not bit == 0: return("inconsistent")
    if not DB[emLen - hLen - sLen - 2] == 1: return("inconsistent")
    salt = bytes([DB[-sLen]]) if sLen > 0 else b""
    M2 = b"\x00"*8 + mHash + salt
    H2 = Hash(M2).digest()
    return("consistent" if H == H2 else "inconsistent")

def RSASSA_PSS_SIGN(private_key, M):
    n, d = (private_key.n, private_key.d)
    k = (len(hex(n)[2:])+(len(hex(n)[2:])%2))//2
    modBits = k * 8
    EM = EMSA_PSS_ENCODE(M, modBits - 1)
    m = OS2IP(EM)
    s = RSASP1(private_key, m)
    S = I2OSP(s, k)
    return(S)

def RSASSA_PSS_VERIFY(public_key, M, S):
    n, e = (public_key.n, public_key.e)
    k = (len(hex(n)[2:])+(len(hex(n)[2:])%2))//2
    modBits = k * 8
    if not len(S) == k: raise ValueError("invalid signature")
    s = OS2IP(S)
    m = RSAVP1(public_key, s)
    emLen = math.ceil((modBits - 1) / 8)
    EM = I2OSP(m, emLen)
    Result = EMSA_PSS_VERIFY(M, EM, modBits - 1)
    return("valid signature" if Result == "consistent" else "invalid signature")

def GENERATE_KEY_PAIR(size=2048):
    p, q = _get_two_primes(size//2)
    n = _get_n(p, q)
    c = _get_carmichaels(p, q)
    e = _get_e(c)
    d = _get_modinv(e, c)
    dp = d % (p-1)
    dq = d % (q-1)
    invq = _get_modinv(q,p)
    return(RSA_public_key(n, e), RSA_private_key(n, d, p, q, invq))

def READ_PUBLIC_KEY_FILE(filename):
    print("reading public key")
    with open(filename, "r") as f:
        c = 0
        lines = []
        comment = ""
        comment_next_line = False
        start = 0
        end = 0
        valid_file = 0
        for line in f:
            if "---- BEGIN" in line:
                start = c + 2
                valid_file += 1
            elif line[:9] == "Comment: ":
                comment += line[9:].replace("\n","")
                if comment[-1:] == "\\":
                    comment = comment[:-1]
                    start += 1
                    comment_next_line = True
            elif comment_next_line:
                comment += line.replace("\n","")
                if comment[-1:] == "\\":
                    comment = comment[:-1]
                    start += 1
                else:
                    comment_next_line = False
            elif "---- END" in line:
                end = c
                valid_file += 1
            lines.append(line)
            c += 1
    pub = "".join(lines[start:end]).replace("\n","")
    messages = from_bytes_prepended(base64.b64decode(pub.encode()))
    try:
        print("key type:",messages[0].decode())
        print("comment:",comment)
        public_key = RSA_public_key(OS2IP(messages[2]), OS2IP(messages[1]))
    except:
        valid_file = 0
    if not valid_file == 2:
        raise Exception("file error")
    print("read public key success")
    return(public_key)

def READ_PRIVATE_KEY_FILE(filename, dialog=False, userinput=None, appparent=None):
    print("reading private key")
    with open(filename, "r") as f:
        c = 0
        lines = []
        comment = None
        comment_next_line = False
        comment_printed = False
        key = None
        valid_file = 0
        checksum_index = 0
        for line in f:
            if "dac-key-file-" in line:
                file_version = re.search("(\d.\d+)(?=:)",line).group(0)
                key_size = re.search("\d+$",line).group(0)
                print("file version: {}\nkey size: {}".format(file_version, key_size))
                if not file_version == version:
                    print("file may not be compatible, latest version: {}".format(version))
                valid_file += 1
            elif "Encryption: " in line:
                if line[12:].replace("\n","") == "dac-vig-AES":
                    print("file encrypted with dac-vig-AES")
                    if not dialog:
                        key = getpass.getpass("enter file decryption key: ").encode()
                    else:
                        key = userinput("Unlock Private Key", "enter file decryption key:", parent=appparent).encode()
                else:
                    print("file not encrypted")
                    key = b""
                valid_file += 1
            elif "Comment:" in line:
                comment = ""
                valid_file += 1
                comment += line[9:].replace("\n","")
                if comment[-1:] == "\\":
                    comment = comment[:-1]
                    comment_next_line = True
            elif comment_next_line:
                comment += line.replace("\n","")
                if comment[-1:] == "\\":
                    comment = comment[:-1]
                else:
                    comment_next_line = False
            if not comment == None and not comment_next_line and not comment_printed:
                print("comment:",comment)
                comment_printed = True
            elif "Public-Lines" in line:
                public_lines = (c,int(re.search("(\d+)$",line).group(0)))
                valid_file += 1
            elif "Private-Lines" in line:
                private_lines = (c,int(re.search("(\d+)$",line).group(0)))
                valid_file += 1
            elif "Private-MAC" in line:
                file_MAC = line[-41:].replace("\n","")
                print("private-hmac:    {}".format(file_MAC))
                valid_file += 1
                checksum_index = c
            lines.append(line)
            c += 1
    print("calculated hmac: {}".format(hexl(hmac(key, b"".join(i.encode() for i in lines[:checksum_index]))).decode()))
    if hexl(hmac(key, b"".join(i.encode() for i in lines[:checksum_index]))).decode() == file_MAC:
        valid_file += 1
    else:
        print("file hash incorrect")
    pub = "".join(lines[public_lines[0]+1:public_lines[0]+public_lines[1]+1]).replace("\n","")
    priv = "".join(lines[private_lines[0]+1:private_lines[0]+private_lines[1]+1]).replace("\n","")
    if key:
        c = AESCipher(key)
        priv = base64.b64encode(_vigenere_m(c.decrypt(base64.b64decode(priv.encode())),key, True)).decode()
    try:
        pub_list = [OS2IP(i) for i in from_bytes_prepended(base64.b64decode(pub.encode()))]
        priv_list = [OS2IP(i) for i in from_bytes_prepended(base64.b64decode(priv.encode()))]
        public_key = RSA_public_key(pub_list[2], pub_list[1])
        private_key = RSA_private_key(pub_list[2], priv_list[0], priv_list[1], priv_list[2], priv_list[3])
    except Exception as e:
        valid_file = 0
        print(e)
        return()
    if not valid_file == 7:
        #raise Warning("file error")
        #raise Exception("file error")
        print("file error")
    print("read private key success {}".format("with warnings" if not valid_file == 7 else ""))
    return(public_key, private_key)

def WRITE_PUBLIC_KEY_FILE(filename, public_key, comment=""):
    with open(filename, "wb") as f:
        f.write(b"---- BEGIN PUBLIC KEY ----\n")
        precomment = "Comment: \"{}\"\n".format(comment)
        comment = ""
        for i in range(0, len(precomment), 63):
            comment += precomment[i:i+63]+("\\\n" if len(precomment[i:i+63]) >= 63 else "")
        f.write(comment.encode())
        DB = base64.b64encode(b"".join(to_bytes_prepended(m) for m in [b"dac-rsa",public_key.e,public_key.n]))
        lines = [DB[i:i+64] for i in range(0, len(DB), 64)]
        for line in lines:
            f.write(line+b"\n")
        f.write(b"---- END PUBLIC KEY ----\n")

def WRITE_PRIVATE_KEY_FILE(filename, public_key, private_key, encrypt=False, comment=""):
    if private_key.p == None:
        raise ValueError("private key not complete")
    DB = b""
    with open(filename, "wb") as f:
        DB+="dac-key-file-v{}: dac-rsa-{}\n".format(version, len(hex(public_key.n)[2:])*4).encode()
        DB+="Encryption: {}\n".format("none" if not encrypt else "dac-vig-AES").encode()
        precomment = "Comment: \"{}\"\n".format(comment)
        comment = ""
        for i in range(0, len(precomment), 63):
            comment += precomment[i:i+63]+("\\\n" if len(precomment[i:i+63]) >= 63 else "")
        DB+=comment.encode()
        public_blob = base64.b64encode(to_bytes_prepended([b"dac-rsa",
                                                           public_key.e,
                                                           public_key.n]))
        lines = [public_blob[i:i+64] for i in range(0, len(public_blob), 64)]
        DB+='Public-Lines: {}\n'.format(len(lines)).encode()
        for b in lines:
            DB+=b+b"\n"
        private_blob = base64.b64encode(to_bytes_prepended([private_key.d,
                                                            private_key.p,
                                                            private_key.q,
                                                            private_key.invq]))
        if encrypt:
            key = getpass.getpass("enter file encryption key: ").encode()
            if not key == b"":
                c = AESCipher(key)
                private_blob = base64.b64encode(c.encrypt(_vigenere_m(base64.b64decode(private_blob),key)))
            else:
                DB = DB.replace(b"dac-vig-AES",b"none")
        else:
            key = b""
        lines = [private_blob[i:i+64] for i in range(0, len(private_blob), 64)]
        DB+='Private-Lines: {}\n'.format(len(lines)).encode()
        for b in lines:
            DB+=b+b"\n"
        DBHMAC = hexl(hmac(key,DB)).decode()
        print("Writen hmac: {}".format(DBHMAC))
        DB+='Private-MAC: {}\n'.format(DBHMAC).encode()
        f.write(DB)

def WRITE_BOTH_KEY_FILES(file_name, public_key, private_key, comment=""):
    if not file_name:
        file_name = input("file name: ")
    ts = datetime.datetime.fromtimestamp(time.time()).strftime('%Y%m%d-%H%M%S')
    comment = comment if not comment == "" else input("file comment: ")
    WRITE_PUBLIC_KEY_FILE(file_name+".publ", public_key, comment+" "+ts)
    WRITE_PRIVATE_KEY_FILE(file_name+".priv", public_key, private_key, False, comment+" "+ts)

def SIGN_FILE(filename, private_key):
    f = open(filename, "rb").read()
    y = base64.b64encode(RSASSA_PSS_SIGN(private_key, f))
    x = b"#---- BEGIN SIGNATURE ----\r\n#"+b"#".join(y[i:i+64]+b"\r\n" for i in range(0, len(y), 64))+b"#---- END SIGNATURE ----"
    with open(filename+".signed", "wb") as j:
        #j.write(f)
        j.write(x)

def VERIFY_FILE(filename, public_key):
    with open(filename,"rb") as f:
        file = f.read()
    with open(filename+".signed", "rb") as f:
        lines = []
        signature_start = 0
        signature_end = 0
        counter = 0
        for line in f:
            lines.append(line)
            if b"#---- BEGIN SIGNATURE ----\r\n" == line:
                signature_start = counter
            elif b"#---- END SIGNATURE ----" == line:
                signature_end = counter
            counter += 1
        signature = b"".join(line for line in lines[signature_start+1:signature_end]).replace(b"\r\n",b"").replace(b"#",b"")
        S = base64.b64decode(signature)
        print(RSASSA_PSS_VERIFY(public_key, file, S))


class AESCipher():
    def __init__(self, key, keyderivation = 'pbkdf2_hmac'):
        self.bs = 16
        if keyderivation == 'pbkdf2_hmac':
            self.key = hashlib.pbkdf2_hmac('sha256', key, b"Salty little addition", 100000)
        elif keyderivation == 'sha256':
            self.key = hashlib.sha256(key+"salty litte addition".encode()).digest()

    def encrypt(self, raw, iv=None):
        raw = self._pad(raw)
        if iv == None:
            iv = bytes([secure_random.getrandbits(8) for i in range(AES.block_size)])
        cipher = AES.new(self.key, AES.MODE_CBC, iv)
        return(iv + cipher.encrypt(raw))

    def decrypt(self, enc):
        iv = enc[:AES.block_size]
        cipher = AES.new(self.key, AES.MODE_CBC, iv)
        return(self._unpad(cipher.decrypt(enc[AES.block_size:])))

    def _pad(self, s):
        return(s+(self.bs-len(s) % self.bs) * chr(self.bs - len(s) % self.bs).encode())

    @staticmethod
    def _unpad(s):
        return(s[:-ord(s[len(s)-1:])])

def lock_file(file, key):
    c = AESCipher(key)
    open(file+".lock", "wb").write(c.encrypt(open(file, "rb").read()))

def unlock_file(file, key):
    c = AESCipher(key)
    open(file, "wb").write(c.decrypt(open(file+".lock", "rb").read()))

def AESCipherE_LV(m, key, iv=None):
    c = AESCipher(bytes(key))
    return(list(c.encrypt(bytes(m), bytes(iv))))

def AESCipherD_LV(e, key):
    c = AESCipher(bytes(key))
    return(list(c.decrypt(bytes(e))))

def GENERATE_AUTHENTICATED_MESSAGE(message, recipient, local_private_key, recipient_public_key, key):
    signature = RSASSA_PSS_SIGN(local_private_key, recipient+message)
    message = to_bytes_prepended([recipient,message,signature])
    c = AESCipher(key)
    return(c.encrypt(message))

def PARSE_AUTHENTICATED_MESSAGE(message, local_private_key, sender_public_key, key):
    c = AESCipher(key)
    recipient, message, signature = from_bytes_prepended(c.decrypt(message))
    print("intended recipient: {}".format(recipient.decode()))
    print("message: {}".format(message.decode()))
    verify = RSASSA_PSS_VERIFY(sender_public_key, recipient+message, signature)
    print(verify)
    return(message)


class DHServer():
    def __init__(self):
        self.stage = 0
        self.p = None
        self.g = None
        self.X = None
        self.A = None
        self.B = None
        self.shared_secret = None

    def gen_XpgA(self):
        if not self.stage == 0: return("DH failure 1")
        self.X = secure_random.getrandbits(1024)
        self.p = _get_prime(2048)
        self.g = 3
        self.A = pow(self.g, self.X, self.p)
        self.stage = 1
        return("DH success")

    def get_pgA(self):
        return(self.p, self.g, self.A)

    def set_B(self, B):
        if not self.stage == 1: return("DH failure 2")
        self.B = B
        self.stage = 2
        return("DH success")

    def gen_s(self):
        if not self.stage == 2: return("DH failure 3")
        self.shared_secret = pow(self.B, self.X, self.p)
        self.stage = 3
        return("DH success")

    def get_s(self):
        return(self.shared_secret if self.stage == 3 and not self.shared_secret == None else "DH failure 4")

class DHClient():
    def __init__(self):
        self.stage = 0
        self.p = None
        self.g = None
        self.X = None
        self.A = None
        self.B = None
        self.shared_secret = None

    def gen_X(self):
        if not self.stage == 0: return("DH failure 1")
        self.X = secure_random.getrandbits(1024)
        self.stage = 1
        return("DH success")

    def set_pgA(self, pgA):
        if not self.stage == 1: return("DH failure 2")
        self.p, self.g, self.A = pgA
        self.stage = 2
        return("DH success")

    def gen_B(self):
        if not self.stage == 2: return("DH failure 3")
        self.B = pow(self.g, self.X, self.p)
        self.stage = 3
        return("DH success")

    def get_B(self):
        return(self.B if not self.B == None else "DH failure 4")

    def gen_s(self):
        if not self.stage == 3: return("DH failure 5")
        self.shared_secret = pow(self.A, self.X, self.p)
        self.stage = 4
        return("DH success")

    def get_s(self):
        return(self.shared_secret if self.stage == 4 and not self.shared_secret == None else "DH failure 6")

if __name__ == "__main__":
    a = READ_PUBLIC_KEY_FILE("BuildVerifyKey.publ")
    #WRITE_BOTH_KEY_FILES("BuildVerifyKey", a,b,"build verification key")
    #SIGN_FILE("..\\buildtools\\dist\\AutoMacro\\AutoMacro.exe",b)
    VERIFY_FILE("..\\buildtools\\dist\\AutoMacro\\AutoMacro.exe",a)
