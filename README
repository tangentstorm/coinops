**coinops** is a repo for experimenting with optimization of
freepascal code via x86-64 assembly language, using an iterated
sha256 program (the hashing algorithm used in bitcoin) as a subject.

This **junkops** branch contains an experiment that shows how
adding useless junk operations (moving the contents of an arbitrary
register into ram) can increase the speed of the executed code.

A compiler flag is used to toggle the inclusion of several lines
in sha256_mjw.pas, starting on (line 64)[https://github.com/tangentstorm/coinops/blob/junkops/sha256_mjw.pas#L164].

    avg time(ms) with -dJUNKOPS: 1822.84ms
    avg time(ms) without:        1836.44ms

**Why would adding extra useless operations to the code speed it up?**

*I have no idea.* Hopefully someone out there can explain:

http://stackoverflow.com/questions/17896714/why-would-introducing-useless-mov-instructions-speed-up-a-tight-loop-in-x86-64-a

To run the experiment for yourself, you need free pascal for x86_64
from http://freepascal.org/ as well as python to run the experiment.
