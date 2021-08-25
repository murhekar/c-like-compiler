#!/bin/bash
clean=$2
direc=$1
for f in "$direc"/*.c
do
	# echo $f
	name=$(basename $f)
	echo $name
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
	# diff "$f".my.error.txt "$f".ref.error.txt
done
if [ "$clean" == "c" ]
	then
	rm "$direc"/*.error.*
	rm "$direc"/*.ic
	rm "$direc"/*.s
	rm "$direc"/*.out
fi