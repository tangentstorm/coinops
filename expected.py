"""
python implementation of the code in sha256_mjw.pas
used for a (manual) sanity check to make sure the
result is right.
"""
from __future__ import print_function
import sys
from hashlib import sha256

def recursive_sha256(n, s="0123456789ABCDEF0123456789ABCDEF"):
    d = sha256(s)        # this is the first application
    for i in range(n-1): # so subtract one from total up front
        d = sha256(d.digest())
    return d.hexdigest()

if __name__=='__main__':
    if len(sys.argv) == 2:
        try: n = int(sys.argv[1])
        except: print("usage: expected [n]")
    else: n = 2 ** 20
    print('expected result for n = %i:' % n)
    print(recursive_sha256(n))

