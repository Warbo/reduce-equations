#!/usr/bin/env bash

MSG="cabal build"
if OUTPUT=$(cabal build 2>&1)
then
    echo "ok - $MSG"
else
    echo "$OUTPUT" 1>&2
    echo "not ok - $MSG"
fi

MSG="cabal test"
if OUTPUT=$(cabal test 2>&1)
then
    echo "ok - $MSG"
else
    echo "$OUTPUT" 1>&2
    echo "not ok - $MSG"
fi

for F in test/data/*.json
do
    MSG="Reducing $F"
    if OUTPUT=$(cabal run -v0 reduce-equations < "$F" 2>&1)
    then
        echo "ok - $MSG"
    else
        echo "$OUTPUT" 1>&2
        echo "not ok - $MSG"
    fi

    MSG="Got equations from $F"
    if echo "$OUTPUT" | grep "==" > /dev/null
    then
        echo "ok - $MSG"
    else
        echo "$OUTPUT" 1>&2
        echo "not ok - $MSG"
    fi
done

exit 0
