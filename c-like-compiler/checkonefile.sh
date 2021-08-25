#!/bin/bash
f=$1
./sclp -d -ast -icode "$f" > "$f".my.ic 2> "$f".my.error.txt
./sclp -d "$f" > "$f".my.s
./sclp14 -d -ast -icode "$f" > "$f".ref.ic 2> "$f".ref.error.txt
./sclp14 -d "$f" > "$f".ref.s
# ./sclp -d -ast -icode "$f" > "$f".my.ic 2> "$f".my.error.txt
# ./sclp -d "$f" > "$f".my.s
# ./sclp16 -d -ast -icode "$f" > "$f".ref.ic 2> "$f".ref.error.txt
# ./sclp16 "$f" > "$f".ref.s
spim -file "$f".my.s > "$f".my.out
spim -file "$f".ref.s > "$f".ref.out
diff "$f".my.out "$f".ref.out
if [ "$2" == "c" ] 
	then
	rm "$f".*.error.*
    rm "$f".*.ic
    rm "$f".*.s
    rm "$f".*.out
fi