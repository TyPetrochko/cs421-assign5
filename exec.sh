#!/bin/sh
/c/cs421/bin/sml <<EOF 2> /dev/null | egrep -v '\- |val it = |val use = |Standard|\[(linking|library|loading|scanning)'  
    CM.make "sources-mine.cm";
    Main.comp "$1";
EOF

# echo "CM.make \"sources.cm\"; PP.TS \"$1\"; Parse.parse \"$1\";" | /c/cs421/bin/sml;
