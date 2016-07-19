#!/bin/python
# -*- coding: utf-8 -*-
# vim:set ts=8 sts=8 sw=8 tw=80 noet cc=80:

from random import shuffle
import mono

tin = "".join([ chr(x) for x in range(ord("a"), ord("z")) ])
tout = [ c for c in tin ]
shuffle(tout)
tout = "".join(tout)
print("%s -> %s" % (tin, tout))

rtxt = "hallo welt das ist ein langer text auf deutsch der geknackt werden soll"
rtxt2 = "also meines kann es knacken. Den Text von vorhin z.B. kann es voll " \
		"automatisch knacken, und es sagt dir dann die Top n Treffer"

ctxt = ["knbcrvvc qjc na nrwojlq tnrwn Jqwdwp"]

def run(rtxt):
	rtxt = rtxt.lower()

	text = rtxt.translate(str.maketrans(tin, tout))
	decode(text)

def decode(text):
	print("encrypted: '%s'" % text)

	translations = mono.crack(text, "de")

	#print("trans: %s" % trans)

	def translate(c, trans):
		l = c.lower()
		if l in trans:
			return trans[l] if l == c else trans[l].upper()
		return c

	for trans in translations:
		out = "".join([ translate(c, trans) for c in text ])
		print(out)

for t in [rtxt, rtxt2]:
	run(t)

for t in ctxt:
	decode(t)
