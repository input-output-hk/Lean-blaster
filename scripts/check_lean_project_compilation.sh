#!/usr/bin/env bash

exec_found=0
if [[ $# -eq 1 ]]
then
  PROJECT_NAME=$1
  LEAN_FILES=`find . -name '*.lean' | grep -v lakefile.lean`
  EXEC_FILES=`cat lakefile.lean | grep root | sed 's/root := .//g'`
  # clean lean project
  lake clean
  # build lean project with log
  echo "Building Lean project $PROJECT_NAME ..."  
  lake build $PROJECT_NAME 2>&1 | tee build.log
  if [[ $? -ne 0 ]]
  then
    cat build.log
    exit 1
  fi
  for i in $LEAN_FILES
  do
   LEAN_MODULE=`echo $i | sed 's/\.\///g' | sed 's/\//./g' | sed 's/.lean//g'`
   RES=`cat build.log | grep -o "Built $LEAN_MODULE"`
   for j in $EXEC_FILES
    do
     if [[ $LEAN_MODULE = $j ]]
     then
      let "exec_found=1"
     fi
    done
   if [[ $RES = "" ]] && [ "$exec_found" -eq 0 ]
   then
     echo "Lean module $LEAN_MODULE NOT compiled !!!"
     exit 1
   fi
   let "exec_found=0"
  done
  # rm build log
  rm -rf build.log
else
cat <<EOF
 usage: check_lean_project_compilation.sh <PROJECT NAME>
EOF
fi
