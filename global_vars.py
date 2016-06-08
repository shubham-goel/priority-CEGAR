def init():
	global variable_number
	global variable_name_to_number
	global hex2bin
	global bin2hex
	global float_dec2bin_dict
	variable_number = 1
	variable_name_to_number = {}
	hex2bin = dict('{:x} {:04b}'.format(x,x).split() for x in range(16))
	bin2hex = dict('{:b} {:x}'.format(x,x).split() for x in range(16))
	float_dec2bin_dict = {}
