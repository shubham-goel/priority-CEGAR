#!/bin/bash
while [[ 1 -eq 1 ]]; do
	flag=1
	for pid in $(ps -ef | grep "[^c] \./sharpSAT" | awk '{print $2}'); do
		echo "killing sharpSAT process $pid"
		kill -9 $pid
		flag=0
		break
	done
	if [[ $flag -eq 1 ]]; then
		break
	fi
done
