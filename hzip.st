#!/afs/cats.ucsc.edu/courses/cmps112-wm/usr/smalltalk/bin/gst -f
RCSID := '$Id: hzip.st$'.
nl := Character nl.

"Compression Algorithm based on Huffman Coding"


"catfile.st"
FileStream extend [
   nl := Character nl.
   catFile [
      |count|
      count := 0.
      [self atEnd not] whileTrue: [
         |padded|
         count := count + 1.
         padded := count printPaddedWith: Character space to: 6.
         stdout << padded << ': ' << self nextLine << nl.
      ]
   ]
    "
    Part (a) in Compression.
    Using example code from charfreq.st (lines 63 - 67)
    "
   initFreqTable [
       |freqTable|
       "0 to 255 elements (256) + EOF Element (1)"
       freqTable := ZeroArray new: 257.
       [self atEnd not] whileTrue: [
           |ordChar|
           ordChar := self next asInteger.
           freqTable incr: ordChar.
       ].
       "put 1 at index 256 to indicate EOF"
       freqTable at: 256 put: 1.
       ^freqTable
   ]
]

"charfreq.st"
Object subclass: ZeroArray [
   |theArray|

   ZeroArray class >> new [
      self shouldNotImplement.
   ]

   ZeroArray class >> new: size [
      |result|
      result := super new.
      result init: size.
      ^ result
   ]

   init: size [
      theArray := Array new: size.
   ]

   size [
      ^ theArray size.
   ]

   at: index [
      ^ theArray at: index + 1.
   ]

   at: index put: value [
      ^ theArray at: index + 1 put: value.
   ]

   incr: index [
      (self at: index) isNil
         ifTrue: [ self at: index put: 0].
      self at: index put: (self at: index) + 1.
   ]

   keysAndValuesDo: aBlock [
      (0 to: (self size) - 1) do: [:index |
         aBlock value: index value: (self at: index).
      ]
   ]
]

"tree part b of compression from pdf"
Object subclass: Leaf [
   |char count|
   char [ ^ char ]
   count [ ^ count ]

   Leaf class >> new [
      self shouldNotImplement
   ]

   Leaf class >> new: aChar count: aCount [
      |result|
      result := super new.
      result setChar: aChar andCount: aCount.
      ^result
   ]

   setChar: aChar andCount: aCount [
      char := aChar.
      count := aCount.
   ]

   <= other [
      ^ (count < other count)
      | ((count = other count) & (char <= other char))
   ]

   printBase: aStream [
      ^ aStream << self class << '(' << char << ',' << count
   ]

   printOn: aStream [
      (self printBase: aStream) << ')'.
   ]

   inorder: visitor prefix: string [
      visitor value: char value: string.
   ]

]

Leaf subclass: Tree [
   |left right|

    getLeft [ ^ left]
    getRight [^ right]

   Tree class >> new: aChar count: aCount [
      self shouldNotImplement
   ]

   Tree class >> new: aChar count: aCount left: aLeft right: aRight [
      |result|
      result := super new: aChar count: aCount.
      result setLeft: aLeft andRight: aRight.
      ^ result
   ]

   setLeft: aLeft andRight: aRight [
      left := aLeft.
      right := aRight.
   ]

   printOn: aStream [
      (self printBase: aStream) << ',' << left << ',' << right << ')'.
   ]

   inorder: visitor prefix: string [
      left inorder: visitor prefix: string, '0'.
      right inorder: visitor prefix: string, '1'.
   ]

]

"from bitstream.st"
Object subclass: BitStream [
   |bitIndex byte myStream|
   BitStream class >> new: fileStream [
      |result|
      result := super new.
      result init: fileStream.
      ^result
   ]
   init: fileStream [
      myStream := fileStream.
      bitIndex := 1.
   ]
   nextBit [
      bitIndex = 1 ifTrue: [
         byte := myStream next.
         bitIndex := 9.
      ].
      bitIndex := bitIndex - 1.
      ^byte value bitAt: bitIndex
   ]
   atEnd [
      ^bitIndex = 1 and: [myStream atEnd]
   ]
]
"from outbits.st"
Object subclass: OutBits [
   |bitIndex currentByte myStream|
   OutBits class >> new [
      self shouldNotImplement.
   ]
   OutBits class >> new: fileStream [
      |result|
      result := super new.
      result init: fileStream.
      ^result
   ]
   clearByte [
      bitIndex := 8.
      currentByte := 0.
   ]
   init: fileStream [
      myStream := fileStream.
      self clearByte.
   ]
   flushByte [
      bitIndex = 8 ifFalse: [
         myStream nextPutByte: currentByte.
         self clearByte.
      ]
   ]
   writeBit: bit [
      currentByte := currentByte bitAt: bitIndex put: bit.
      bitIndex := bitIndex - 1.
      bitIndex = 0 ifTrue: [self flushByte].
   ]
]


"Checking correct number of args from bytecopy.st"
"
(((Smalltalk arguments size) > 0) & ((Smalltalk arguments size) < 4)) ifFalse: [
    ObjectMemory quit
].
"
|getOp iFileName oFileName|
getOp := Smalltalk arguments at: 1.
iFileName := Smalltalk arguments at: 2.
oFileName := Smalltalk arguments at: 3.

inputFile := inputFile := FileStream open: iFileName mode: FileStream read.
"If there is an arg for output file then set else stdout"
(oFileName ~= nil) ifTrue: [
    outputFile := FileStream open oFileName mode: FileStream write.
]
ifFalse: [
    outputFile := stdout.
]
|pqueue|
pqueue := SortedCollection new.
"Turns debug on to view debug information"
dOp := FALSE.
(getOp includes: $d) ifTrue: [
    stdout << 'op: d' << nl.
    dOp := TRUE.
]
"---------------------Main-------------------------"
((getOp includes: $t) | (getOp includes: $c)) ifTrue: [
    stdout << 'op: t or c' << nl.
    "Init freqTable."
    |freqTable|
    freqTable := inputFile initFreqTable.
    "Add all freq to priority queue"
    freqTable keysAndValuesDo: [:key :val |
    (val notNil and: [val > 0]) ifTrue: [
        pqueue add: (Leaf new: key count: val)]
    ]

]
(getOp includes: $u) ifTrue: [
    stdout << 'op: u' << nl.
]
"---------------------End-------------------------"
"priorityQ := SortedCollection new."

"stdout << 'Hello, World!' << nl.
n := 20.
s := n printPaddedWith: Character space to: 10.
stdout << s << nl."