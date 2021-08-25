#!/bin/bash
clean=$2
direc=$1
for f in "$direc"/*.c
do
	# echo $f
	name=$(basename $f)
	echo $name
	# ./sclp14 -icode "$f" 2> "$f".my.error.txt
	# mv "$f".ic "$f".my.ic
	# ./sclp -icode "$f" 2> "$f".ref.error.txt
	# mv "$f".ic "$f".ref.ic
	./sclp14 -d -icode "$f" > "$f".my.ic 2> "$f".my.error.txt
	./sclp -d -icode "$f" > "$f".ref.ic 2> "$f".ref.error.txt
	diff -bw "$f".my.ic "$f".ref.ic
	# diff "$f".my.error.txt "$f".ref.error.txt
done
if [ "$clean" == "c" ]
	then
	rm "$direc"/*.error.*
	rm "$direc"/*.ic
	rm "$direc"/*.spim
fi