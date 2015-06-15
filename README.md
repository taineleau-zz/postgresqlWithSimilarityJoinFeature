#postgreSQL With Similarity Join Feature

Final project of Introduction to Database course.

Implemented two functions, Levenshtein_Distance and Jaccard_Index, for the Similartiy Join Feature.

A better solution (Ukkonen, 1985) for the calculation of Levenshtein_Distance is implemented with a time complexity of O(n * d), in which d stands for the given threshold of Levenshtein_Distance. Since `d` is considerably small, it could be regarded as a linear algorithm. ^o^

Please look up the `funcapi.c` directly.

##Usage


replace `function.c` in “src/backend/utils/fmgr/funcapi.c” 

replace `pg_proc.h` in “src/include/catalog/pg_proc.h”

run `helper.sh`

(Actually, adding functions to pgsql in this way is not a proper choice since there is a recommended macro method, please look up the manual: http://www.postgresql.org/docs/9.0/static/xfunc-c.html, thanks to jackyyf~)##Report
Not yet :(##Reference
1.  http://www.cs.helsinki.fi/u/ukkonen/InfCont85.PDF2.  http://www.berghel.net/publications/asm/asm.pdf
