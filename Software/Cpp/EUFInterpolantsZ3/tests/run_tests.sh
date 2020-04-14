#!/bin/bash

# This script must be executed 
# from his current directory

cd ./QF_UF
COUNT=0
for directory in $(ls); do 
  if [ -d $directory ]; then
    cd $directory
    for smt_file in $(ls); do
      if [ -f $smt_file ]; then
        COUNT=$(($COUNT + 1))
        LOCAL_COMMAND="./../../../euf_interpolator $smt_file"
        eval "$LOCAL_COMMAND"
        RESULT=$?
        if [ ! "$RESULT" -eq "0" ]; then
          echo "not ok" $(pwd) $smt_file $RESULT
        fi
      fi
    done
    cd ../
  fi
done

echo "Total number of processed cases: " $COUNT
