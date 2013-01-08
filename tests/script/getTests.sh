#!/bin/sh
ORIGIN=$1	# folder containing test cases (check subfolders as well) 
WHITE_LIST=$2	# text file containing the 'white list'
BLACK_LIST=$3	# text file containing the 'black list'
DEST=$4		# destination text file 

want=""

echo "Searching in '$1' and subdirectories"

echo "\nFiles must contains:"

# create the grep query for the white list
for white_list_arg in $(cat $WHITE_LIST) 
do
	echo "  - '$white_list_arg'"
	want="$want| xargs grep -l '$white_list_arg'"
done

dont_want=""
echo "\nFiles must not contain:"

# create the grep query for the black list
for black_list_arg in $(cat $BLACK_LIST) 
do
	echo "  - '$black_list_arg'"
	dont_want="$dont_want| xargs grep -L '$black_list_arg'"
done

# complete the query
list_of_files="find -X $ORIGIN/ -type f -name '*.js' $dont_want$want"

command="cp \$($list_of_files) $DEST"

eval ${command}

res="ls $DEST | wc -w"
echo "\nFound: "
eval $res

echo "Destination folder: $4"