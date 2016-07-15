#!/bin/bash
rm -rf new_results/
mkdir new_results
cd new_results
mkdir old_results
cp -avr ../results/* old_results/
cd ..
rm -rf results
mv new_results results

k=0
for nodes in `seq 10 2 50`;
do
	start_edges1=$((5*$nodes/2))
	end_edges1=$((5*$nodes/2))
	start_edges=${start_edges1%.*}
	end_edges=${end_edges1%.*}

	for edges in `seq $start_edges $end_edges`;
	do
		start_messages=$(($nodes))
		end_messages=$(($nodes))
		for messages in `seq $start_messages $end_messages`;
		do
			start_timeout=$(($nodes))
			end_timeout=$(($nodes))
			for timeout in `seq $start_timeout $end_timeout`;
			do
				l=$(($messages))
				status=1
				while [[  $status -ne 0 ]]; do
					directory="n$nodes-m$messages-e$edges-t$timeout-l$l"
					echo ''
					echo ''
					echo ''
					echo "BEGINNING NEW SETTING"
					echo "Progress : $directory::(10-20)-(10-11)-($start_edges-$end_edges)-($end_timeout-$start_timeout)-$l-$k"
					echo ''
					echo ''
					python ScheduleTwoPathsCEGAR.py $nodes $messages $edges $timeout $l $k -p >output.curr
					status=$?
					echo "Exit Status=$status"
					if [[ $status -eq 0 ]]; then
						mkdir results/$directory
						cp settings.curr "results/$directory/$directory.setting"
						cp output.curr "results/$directory/$directory.output"
						mv "results/$directory.dat" "results/$directory/$directory.dat"
						cd results/
						zip "$directory" "$directory/$directory.setting" "$directory/$directory.output" "$directory/$directory.dat"
						rm -r "$directory"
						cd ..
					elif [[ $status -ne 2 ]]; then
						exit
					fi
					echo 'Sleeping for 2 seconds...'
					sleep 2
				done
			done
		done
	done
done
