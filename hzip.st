#!/afs/cats.ucsc.edu/courses/cmps112-wm/usr/smalltalk/bin/gst -f
RCSID := '$Id: hzip.st$'.
nl := Character nl.

"Compression Algorithm based on Huffman Coding"

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

Character extend [
   isPrint [
      ^ (Character space <= self) & (self <= $~)
   ]
   visible [
       "[^ '$', self asString] getting rid of $ symbol"
        self isPrint ifTrue: [^ self asString]
        ifFalse: [^ self asInteger printStringRadix: 8]
   ]
]

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
       |newTable|
       "0 to 255 elements (256) + EOF Element (1)"
       newTable := ZeroArray new: 257.
       [self atEnd not] whileTrue: [
           |ordChar|
           ordChar := self next asInteger.
           newTable incr: ordChar.
       ].
       "put 1 at index 256 to indicate EOF"
       newTable at: 256 put: 1.
       ^ newTable
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
   "tree.st depthFirst (leaf)"
   depthFirst: visitor prefix: string [
      visitor value: char value: string.
   ]
    "postorder for -c"
    postorder: visitor [
        visitor value: char value: (self isLeaf).
    ]

    isLeaf [^ true]
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
   "tree.st depthFirst (tree)"
    depthFirst: visitor prefix: string [
        left depthFirst: visitor prefix: string, '0'.
        right depthFirst: visitor prefix: string, '1'.
    ]

    postorder: visitor [
        left postorder: visitor.
        right postorder: visitor.
        visitor value: char value: (self isLeaf).
    ]

    isLeaf [^ false]
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
   currByte [
      ^byte
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
(((Smalltalk arguments size) > 1) & ((Smalltalk arguments size) < 4)) ifFalse: [
    stdout << 'Arguments should be between 2 and 3' << nl.
    ObjectMemory quit: 1.
].

|iFileName oFileName|

getOp := Smalltalk arguments at: 1.
iFileName := Smalltalk arguments at: 2.
((Smalltalk arguments size) > 2) ifTrue: [ oFileName := Smalltalk arguments at: 3].

(File exists: iFileName) ifFalse: [
"^iFileName error: 'input file doest not exist'"
    stdout << 'Input File "' << iFileName << '" does not exist' << nl.
    ObjectMemory quit: 1.
].

|inputFile outputFile|

inputFile := FileStream open: iFileName mode: FileStream read.

(oFileName ~= nil) ifTrue: [
    outputFile := FileStream open: oFileName mode: FileStream write.
]
ifFalse: [
    outputFile := stdout.
].

|priorityq|
priorityq := SortedCollection new.
"Turns debug on to view debug information"
dOp := FALSE.
(getOp includes: $d) ifTrue: [
    stdout << 'op: d' << nl.
    dOp := TRUE.
].
"---------------------Main-------------------------"
"op -t,-c 3.compression"
((getOp includes: $t) | (getOp includes: $c)) ifTrue: [
    "stdout << 'op: t or c' << nl."
    |freqTable encodedArr|
    "Init freqTable."
    freqTable := inputFile initFreqTable.
    "Add all freq to priority queue (part b compression) from .charfreq.st"
    freqTable keysAndValuesDo: [:key :val |
        (val notNil and: [val > 0]) ifTrue: [
            nLeaf := Leaf new: key count: val.
            priorityq add: nLeaf.
        ]
    ].
    "huffman tree init (part c compression) - from tree.st"
    [priorityq size > 1] whileTrue: [
        |leftnode rightnode treecount|
        "priority queue so its sorted in ascending (smaller -> left & larger -> right) "
        leftnode := priorityq removeFirst.
        rightnode := priorityq removeFirst.
        treecount := ((leftnode count) + (rightnode count)).
        nTree := Tree new: (leftnode char) count: treecount left: leftnode right: rightnode.
        priorityq add: nTree.
    ].
    "eTree-leaf encoding using dfs (part d compression)"
    encodedArr := ZeroArray new: 257.
    eTree := priorityq  first.
    eTree depthFirst: [:char :string |
       "stdout << '[' << char asInteger << '][' << string << ']' << nl."
       encodedArr at: char asInteger put: string.
    ] prefix:''.
    "-t option (part e compression) similar to charfreq.st"
    (getOp includes: $t) ifTrue: [
        (getOp includes: $d) ifTrue: [
            stdout << '-t option' << nl.
        ].
        encodedArr keysAndValuesDo: [:key :val |
            (val notNil) ifTrue: [
                char := key asCharacter visible.
                getFreq := (freqTable at: key) asString.
                "newline char when key = 10"
                key = 10 ifTrue: [char := 'x0A'].
                "EOF char when key = 256"
                key = 256 ifTrue: [char := 'EOF'].
                (char asString size) = 1 ifTrue: [
                    stdout << ' ' << char asString.
                    1 to: (5 - char asString size) do: [:i | stdout << ' '.].
                ] ifFalse: [
                    stdout << char asString.
                    1 to: (6 - char asString size) do: [:i | stdout << ' '.].
                ].

              """  s := getFreq printPaddedWith: Character space to: 10."""
                n := getFreq asNumber.
                padded := n printPaddedWith: Character space to: 3.
                stdout << padded.
                stdout << ' ' << val << nl.
            ]
        ]
    ]
    ifFalse: [
        stdout << 'not -t option -c option' << nl.
        dTree := ''.
        eTree postorder:[:char :isLeaf |
            "stdout << isLeaf << nl."
            isLeaf ifTrue:[
                (char ~= 256) ifTrue: [
                    char = 0 ifTrue: [
                        dTree := (dTree, '0', '000000000').
                    ] ifFalse: [
                        temp := ''.
                        8 to: 1 by: -1 do: [:i |
                            temp := (temp, ((char bitAt: i) printString)).
                        ].
                        dTree := (dTree, '0', temp).
                    ]
                ] ifFalse: [
                    dTree := (dTree, '0', '100000000').
                ].
            ] ifFalse: [
                dTree := dTree, '1'.
            ].
        ].
    ].
            outputBytes := OutBits new: outputFile.
            "outputFile is either the correct file, or stdout if unspecified"
            1 to: (dTree size) do: [:i |
                currChar := (dTree at: i) asString.
                currInt := currChar asNumber.
                (getOp includes: $d) ifTrue: [
                  stdout << currChar << nl.
                  stdout << 'curr' << (currInt bitAt: 1) << nl.
                ].
                currBit := currInt bitAt: 1.
                outputBytes writeBit: currBit.
            ].
            "part g tree is completely written out"
            outputBytes writeBit: 1.
            inputFile reset.

    """print to stdout """


    "-c option"
    """(getOp includes: $c) ifTrue: [

    ]"""
    inputFile close.
    outputFile close.
].



"op -u"
(getOp includes: $u) ifTrue: [
    (getOp includes: $d) ifTrue: [
        stdout << 'op: u' << nl.
    ].
    fileBits := BitStream new: inputFile.
    bit := fileBits nextBit.
    (bit = 0) ifTrue: [
      """byteval := inputFile nextByte.
      stdout << byteval << nl."""
      byteval := 0.
      1 to:7 do: [:x |
        bit := fileBits nextBit.
      """  stdout << 'bit '<< bit  << nl."""
        byteval := byteval bitShift: 1.
        byteval := byteval + bit.
      ].
      (getOp includes: $d) ifTrue: [
      stdout << 'byte' << byteval << nl.
      ].

      """use ordered collection as a stack"""
      stack := OrderedCollection new.
      stack addFirst: byteval.

    ].
].
"---------------------End-------------------------"
"priority := SortedCollection new."

"stdout << 'Hello, World!' << nl.
n := 20.
s := n printPaddedWith: Character space to: 10.
stdout << s << nl."
