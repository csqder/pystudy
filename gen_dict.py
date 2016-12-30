import random
import time

def generate_string_dict( n ):
	bowl = set()
	while len(bowl)<n:
		s = ''
		lenth = random.randint(3,15)
		for i in range(lenth):
			s += chr(random.randint(33,126))
		bowl.add(s)
		s = ''
	return bowl

def read_dict_from_file( fn ):
	d = {}
	f = open(fn, 'r')
	for line in f:
		k,v = line.split(' ')
		d[k] = v
	f.close()
	return d

if __name__=='__main__':
	t0 = time.time()
	#s = generate_string_dict(2000000)
	#l = list(s)
	d = read_dict_from_file('out.txt')
	td = time.time()-t0
	print( td )
	# f = open('out.txt','w')
	# for i in range(0,len(l),2):
	# 	f.write('%s %s\n'%(l[i], l[i+1]))
	# f.close()
	input('done!')	



