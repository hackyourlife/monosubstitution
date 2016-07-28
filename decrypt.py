#!/bin/python
# -*- coding: utf-8 -*-
# vim:set ts=8 sts=8 sw=8 tw=80 noet cc=80:

import sys
import mono

def decode(text, lang="de", iterations=300, method="sat"):
	print("encrypted: '%s'" % text)

	if method == "sat":
		translations = mono.crack(text, lang, iterations=iterations)
	else:
		translations = mono.crack_tree(text, lang)[:iterations]

	def translate(c, trans):
		l = c.lower()
		if l in trans:
			return trans[l] if l == c else trans[l].upper()
		return c

	for trans in translations:
		out = "".join([ translate(c, trans) for c in text ])
		print(out)

if __name__ == "__main__":
	if len(sys.argv) == 2:
		text = sys.argv[1]
		decode(text)
	elif len(sys.argv) == 4:
		lang = sys.argv[1]
		iterations = int(sys.argv[2])
		text = sys.argv[3]
		decode(text, lang, iterations)
	else:
		lang = sys.argv[1]
		iterations = int(sys.argv[2])
		method = sys.argv[3]
		text = sys.argv[4]
		decode(text, lang, iterations, method)
