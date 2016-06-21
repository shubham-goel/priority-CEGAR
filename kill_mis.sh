#!/bin/bash
while [[ 1 -eq 1 ]]; do
	flag=1
	for pid in $(ps -ef | grep "MIS\.py" | awk '{print $2}'); do
		echo "killing MIS process $pid"
		kill -9 $pid
		flag=0
		break
	done
	if [[ $flag -eq 1 ]]; then
		break
	fi
done
