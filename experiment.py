"""
experiment to gather data about two variations of a program
"""
from __future__ import print_function
import os, sys, random
import expected # in current directory

def die(msg):
    print(msg)
    sys.exit(-1)

def output_of(cmd):
    return os.popen(cmd).read().strip()

def recompile():
    # compile both versions and make sure there's no error.
    ( os.system('fpc           -onormal ./sha256_mjw.pas')
    | os.system('fpc -dJUNKOPS -ojunky  ./sha256_mjw.pas')
    ) == 0 or die("couldn't compile the program")

def check_equality():
    # make sure the actual behavior hasn't changed:
    n = output_of('./normal -n') # number of times to run
    q = output_of('./normal -q') # the resulting hash
    assert output_of('./junky -n') == n, "n values didn't match"
    assert output_of('./junky -q') == q, "hashes didn't match"
    return n

def check_sanity(n):
    # double check that the resuling hash is actually correct :)
    p = expected.recursive_sha256(int(n))
    if q != p:
        print("ERROR: invalid result hash.")
        print("result  :", q)
        print("expected:", p)
        sys.exit()


def avg(vals):
    return sum(vals)/len(vals)


def run_experiment(times):
    versions = [ 'normal', 'junky' ]
    runtimes = { 'normal':[], 'junky':[] }

    for i in range(times):
        # swap the order randomly to avoid any bias caused by the timing
        order = versions[:] if random.randint(0,1) else reversed(versions)
        for variant in order:
            runtimes[variant].append(int(output_of('./%s -t' % variant)))
        print("[%02i/%i]: normal: %4i ms   junkops: %4i ms"
              % (i+1, times,
                 runtimes['normal'][-1],
                 runtimes['junky'][-1] ))
    return runtimes

if __name__=='__main__':
    if "-ok" in sys.argv:
        print("-- skipping self checks and launching experiment")
    else:
        print("-- recompiling variants")  ; recompile()
        print("-- checking equality")     ; n = check_equality()
        print("-- checking result hash ") ; check_sanity(n)
        print("-- all checks passed. proceding to experiment.")
    runtimes = run_experiment(times=25)
    print("-- experiment complete")
    print('avg time(ms) with -dJUNKOPS: %5.2fms' % avg(runtimes['junky']))
    print('avg time(ms) without:        %5.2fms' % avg(runtimes['normal']))
