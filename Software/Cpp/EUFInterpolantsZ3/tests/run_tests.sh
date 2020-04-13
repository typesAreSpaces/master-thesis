#!/bin/bash

cd ./QF_UF
COUNT=0
for directory in $(ls); do 
  if [ -d $directory ]; then
    cd $directory
    for smt_file in $(ls); do
      if [ -f $smt_file ]; then
        # echo "Running z3 on " $smt_file
        COUNT=$(($COUNT + 1))
        $(./../../../euf_interpolator $smt_file)
        RESULT=$?
        if [ ! "$RESULT" -eq "0" ]; then
          echo "not ok" $smt_file $RESULT
        fi
      fi
    done
    cd ../
  fi
done

echo "Total number of processed cases: " $COUNT
