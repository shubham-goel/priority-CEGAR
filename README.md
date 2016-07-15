# priority-CEGAR
A CEGAR framework that solves for message-priorities in a system.

## Usage
A wide vareity of tools have been incorporated into the code. We can choose what tools (or heuristics) to use by modifying the CEGAR function.

```
USAGE:
$ python ScheduleTwoPathCEGAR.py n m e t l k [options]

  n                     Number of Nodes
  m                     Number of Messages
  e                     Number of Edges
  t                     Global timeout
  l                     The minimum number of messages that should reach on time
  k                     The number of edge crashes
                        (Not relevent for scoring forwarding schemes with option --prob)

OPTIONS:
  -h, --help            show this help message and exit
  -l, --load            Load setting from pickle-dumped file 'settings.curr'
  -m, --manual, --custom
                        Load setting from custom file 'custom.settings'
  --nw, --no-weight     Choose paths without weights
  -c, --count           Count the numer of BAD outcomed fault sequences with
                        at most k crashes
  -p, --prob            Score the forwarding scheme that is generated for the
                        setting
```

#### Custom Setting Generation
Specify the graph you want in a file `custom.settings` with format below, and use the `-m` option
```
Edges
<edge1 source-vertex> <edge1 target-vertex>
<edge2 source-vertex> <edge2 target-vertex>
...
Messages
<message1 source-vertex> <message1 target-vertex>
<message2 source-vertex> <message2 target-vertex>
...
```
Each vertex should be refrenced using a non-negative integer
