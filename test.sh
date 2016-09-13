#!/usr/bin/env bash

ERR=0
function report {
    if [[ "$1" -eq 0 ]]
    then
        echo "ok - $2"
    else
        echo "$OUTPUT" 1>&2
        echo "not ok - $2"
        ERR=1
    fi
}

OUTPUT=$(cabal build 2>&1)
report "$?" "cabal build"

OUTPUT=$(cabal test 2>&1)
report "$?" "cabal test"

for F in test/data/*.json
do
    OUTPUT=$(NIX_EVAL_EXTRA_IMPORTS='[("runtime-arbitrary", "TestInstances")]' \
               cabal run -v0 reduce-equations < "$F")
    report "$?" "Reducing $F"

    OUTPUT=$(echo "$OUTPUT" | grep '^{')
    report "$?" "Got equations from $F"
done

exit "$ERR"
