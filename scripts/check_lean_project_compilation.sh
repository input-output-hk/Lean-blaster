#!/usr/bin/env bash

set -o pipefail

exec_found=0
if [[ $# -ge 1 && $# -le 2 ]]
then
  PROJECT_NAME=$1
  BUILD_TARGET=${2:-$PROJECT_NAME}
  if [ ! -d "$PROJECT_NAME" ]
  then
    echo "Lean source tree '$PROJECT_NAME' is not a directory." >&2
    exit 1
  fi
  LEAN_FILES=`find "$PROJECT_NAME" -type f -name '*.lean' 2>/dev/null`
  if [ -z "$LEAN_FILES" ]
  then
    echo "Lean source tree '$PROJECT_NAME' contains no .lean files." >&2
    exit 1
  fi
  EXEC_FILES=`cat lakefile.lean | grep root | sed 's/root := .//g'`
  # build lean project with log
  echo "Building Lean target $BUILD_TARGET (source tree: $PROJECT_NAME) ..."
  lake build "$BUILD_TARGET" 2>&1 | tee build.log
  if [[ $? -ne 0 ]]
  then
    cat build.log
    exit 1
  fi
  for i in $LEAN_FILES
  do
   LEAN_MODULE=`echo $i | sed 's/\.\///g' | sed 's/\//./g' | sed 's/.lean//g'`
   RES=`grep -F "Built $LEAN_MODULE (" build.log`
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
 usage: check_lean_project_compilation.sh <PROJECT NAME> [BUILD TARGET]
EOF
exit 1
fi
