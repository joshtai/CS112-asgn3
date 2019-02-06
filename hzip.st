#!/afs/cats.ucsc.edu/courses/cmps112-wm/usr/smalltalk/bin/gst -f
RCSID := '$Id: hzip.st$'.
nl := Character nl.


stdout << 'Hello, World!' << nl.
n := 20.
s := n printPaddedWith: Character space to: 10.
stdout << s << nl.
