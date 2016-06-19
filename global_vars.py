def init():
	global last_time
	global variable_number
	global variable_name_to_number
	global hex2bin
	global bin2hex
	global float_dec2bin_dict
	global timeout_limit
	global timeout_limit_small
	timeout_limit = 300
	timeout_limit_small = 120
	variable_number = 1
	variable_name_to_number = {}
	hex2bin = dict('{:x} {:04b}'.format(x,x).split() for x in range(16))
	bin2hex = dict('{:b} {:x}'.format(x,x).split() for x in range(16))
	float_dec2bin_dict = {}

def init_successProb():
	global successProb_iter_start_time
	global successProb_iter_end_time
	global successProb_iter_run_time
	successProb_iter_run_time = {}
	successProb_iter_end_time = {}
	successProb_iter_start_time = {}

def process_successProb():
	for key in successProb_iter_start_time.keys():
		tt = successProb_iter_end_time[key][0]-successProb_iter_start_time[key]
		prob = successProb_iter_end_time[key][1]
		successProb_iter_run_time[key] = (tt,prob)
	return successProb_iter_run_time
