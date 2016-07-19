#!/bin/python
# -*- coding: utf-8 -*-
# vim:set ts=8 sts=8 sw=8 tw=80 noet cc=80:

import sys
from random import shuffle

tin = "".join([ chr(x) for x in range(ord("a"), ord("z")) ])
tout = [ c for c in tin ]
shuffle(tout)
tout = "".join(tout)

if __name__ == "__main__":
	print("%s -> %s" % (tin, tout))
	rtxt = sys.argv[1]
	text = rtxt.translate(str.maketrans(tin, tout))
	print(text)
