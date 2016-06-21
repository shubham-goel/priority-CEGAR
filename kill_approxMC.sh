while [[ 1 -eq 1 ]]; do
	flag=1
	for pid in $(ps -ef | grep " \./scalmc" | awk '{print $2}'); do
		echo "killing scalmc process $pid"
		kill -9 $pid
		flag=0
		break
	done
	if [[ $flag -eq 1 ]]; then
		break
	fi
done
