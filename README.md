run

> cargo run --release 12 2>/dev/null | sed 's/.*://' | sort | uniq -c

to get the statistics of boundary genera as in the paper.
The executable takes one even integer between (2 and 24) as input and spits out:

* On stderr: some infos on what the program is doing
* On stdout: the list of maps with given number of darts, + their "boundary genera"
