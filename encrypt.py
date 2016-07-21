#!/bin/python
# -*- coding: utf-8 -*-
# vim:set ts=8 sts=8 sw=8 tw=80 noet cc=80:

import sys
import mono
from random import shuffle

tin = "".join([ chr(x) for x in range(ord("a"), ord("z")) ])
tout = [ c for c in tin ]
shuffle(tout)
tout = "".join(tout)

def mktrans(tin, tout):
	return { tin[i]: tout[i] for i in range(len(tin)) }

def _translate(c, trans):
	l = c.lower()
	if l in trans:
		return trans[l] if l == c else trans[l].upper()
	return c

def translate(text, trans):
	return "".join([ _translate(c, trans) for c in text ])

if __name__ == "__main__":
	print("%s -> %s" % (tin, tout))
	if len(sys.argv) == 3:
		d = mono.get_dict(sys.argv[1])
		words = mono.get_words(sys.argv[2].lower())
		errors = [ word for word in words if word not in d ]
		text = translate(sys.argv[2], mktrans(tin, tout))
		if len(errors) > 0:
			print("warning: those words are not in the dict: %s" % \
					", ".join(errors))
	else:
		text = translate(sys.argv[1], mktrans(tin, tout))
	print(text)
