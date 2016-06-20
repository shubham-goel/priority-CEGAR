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
