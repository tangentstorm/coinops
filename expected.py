from hashlib import sha256

d = sha256("0123456789ABCDEF0123456789ABCDEF")

for n in range(65535): # 65536 - 1 above
    d = sha256(d.digest())

print d.hexdigest()
