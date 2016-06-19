#!/bin/bash

k=1
for nodes in `seq 11 50`;
do
	start_edges=$((3*$nodes))
	end_edges=$((3*$nodes))
	for edges in `seq $start_edges $end_edges`;
	do
		for messages in `seq 10 10`;
		do
			start_timeout=$(($nodes-2))
			end_timeout=$(($nodes-2))
			for timeout in `seq $end_timeout -1 $start_timeout`;
			do
				l=$(($messages))

				directory="$nodes-$messages-$edges-$timeout-$k-$l"
				echo "BEGINNING NEW SETTING"
				echo "Progress : $directory::(10-20)-(10-11)-($start_edges-$end_edges)-($end_timeout-$start_timeout)-$k-$l"
				python ScheduleTwoPathsCEGAR.py $nodes $messages $edges $timeout $k $l -p

			done
		done
	done
done
