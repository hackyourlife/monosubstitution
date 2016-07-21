# -*- coding: utf-8 -*-
# vim:set ts=8 sts=8 sw=8 tw=80 noet cc=80:

import re
import z3

frequencies_de = [ 6.516, 1.886, 2.732, 5.076, 16.396, 1.656, 3.009, 4.577,
		6.55, 0.268, 1.417, 3.437, 2.534, 9.776, 2.594, 0.67, 0.018,
		7.003, 7.27, 6.154, 4.166, 0.846, 1.921, 0.034, 0.039, 1.134]
frequencies_de_utf = { "ä": 0.578, "ö": 0.443, "ü": 0.995, "ß": 0.307 }

frequencies_en = [ 8.167, 1.492, 2.782, 4.253, 12.702, 2.228, 2.015, 6.094,
		6.966, 0.153, 0.772, 4.025, 2.406, 6.749, 7.507, 1.929, 0.095,
		5.987, 6.327, 9.056, 2.758, 0.978, 2.361, 0.15, 1.974, 0.074 ]

def merge_dicts(*dicts):
	r = {}
	for d in dicts:
		r.update(d)
	return r

def default_frequencies(lang):
	def basic_frequencies(table):
		return { chr(i + 97): table[i] / 100.0 \
				for i in range(len(table)) }
	def scale(table):
		return { c: table[c] / 100.0 for c in table }

	if lang == "en":
		return basic_frequencies(frequencies_en)
	if lang == "de":
		return merge_dicts(basic_frequencies(frequencies_de),
				scale(frequencies_de_utf))
	raise ValueError("no frequency table for language \"%s\"" % lang)

dicts = {}
def _read(path):
	with open(path) as f:
		return [ l.strip().lower() for l in f.readlines() \
				if len(l.strip()) > 0 ]

def _get_dict(lang):
	if lang == "de":
		return set(_read("/usr/share/dict/german") +
				_read("german.dic"))
		#return set(_read("/usr/share/dict/german"))
	if lang == "en":
		return set(_read("/usr/share/dict/british-english"))
	raise ValueError("no dict for language \"%s\"" % lang)

def get_dict(lang):
	if lang in dicts:
		return dicts[lang]
	dicts[lang] = _get_dict(lang)
	return dicts[lang]

def is_supported(lang):
	try:
		default_frequencies(lang)
	except:
		return False
	try:
		get_dict(lang)
	except ValueError:
		return False
	return True

def frequencies(text, letters):
	f = { l: text.count(l) for l in set(text) if l in letters }
	s = sum([ v for (c, v) in f.items() ])
	return { l: f[l] / s for l in f }

def cost(text, freq):
	tf = frequencies(text, freq)
	t = [ (tf[c] - f) ** 2 for (c, f) in freq.items() if c in tf ]
	return sum(t) / len(t)

################################################################################
# MONOALPHABETIC SUBSTITUTION
################################################################################
ascii_only = re.compile(r"\W")
def get_pattern(word):
	word = ascii_only.sub(" ", word).lower()
	l = {}
	pattern = ""
	for c in word:
		if not c in l:
			l[c] = chr(len(l) + 65)
		pattern += l[c]
	return pattern
	#return [ ord(i) - ord(word[0]) for i in word ]

pattern_dicts = {}
def get_pattern_dict(lang):
	if lang in pattern_dicts:
		return pattern_dicts[lang]
	d = get_dict(lang)
	pattern_dicts[lang] = {}
	for w in d:
		p = get_pattern(w)
		if p in pattern_dicts[lang]:
			pattern_dicts[lang][p] += [ w ]
		else:
			pattern_dicts[lang][p] = [ w ]
	return pattern_dicts[lang]

def get_words(text):
	return [ w.strip() for w in ascii_only.sub(" ", text).split(" ")
				if len(w.strip()) > 1 ]

def get_replacement(cipher, plain, l):
	return plain[cipher.index(l)]

def get_letter(letter):
	return "c%d" % ord(letter)

def distinct(literals):
	clauses = []

	for literal in literals:
		clause = [ l if l == literal else "(not %s)" % l \
					for l in literals ]
		clauses += [ "(and %s)" % " ".join(clause) ]

	return "(or %s)" % " ".join(clauses)

# Formulas have this basic structure (Cn = n-th candidate word)
# ((atob and btoc) or (atoc and btod)) and ((atob and btoc) or (atod and btox))
#   WORD 1/C1          WORD 1/C2             WORD 2/C1          WORD 2/C2

# Strategy:
# 1) get candidate words by looking at the pattern/structure
# 2) build a replacement table per word
# 3) combine the replacement tables to a SAT formula
# 4) append the one-hot requirement
# 5) solve using a SAT solver
def crack(text, lang, top=5, iterations=300):
	text = text.lower()

	d = get_dict(lang)
	patterns = get_pattern_dict(lang)
	words = get_words(text)

	lang_freq = default_frequencies(lang)
	#text_freq = frequencies(text, lang_freq)
	#top_text = sorted(text_freq, key=lambda x: text_freq[x])
	#top_lang = sorted(lang_freq, key=lambda x: lang_freq[x])

	#print(top_text)
	#print(top_lang)

	#top_in_text = top_text[-1]
	#top_in_lang = top_lang[-1]
	#print("%s -> %s" % (top_in_text, top_in_lang))

	#text_pattern = [ get_pattern(word) for word in words ]
	#candidates = [ patterns[pattern] for pattern in text_pattern ]

	input_letters = set("".join(words))
	output_letters = set([ c for w in d for c in w ])

	smt = []
	# define variables
	for li in input_letters:
		for lo in output_letters:
			smt += ["(declare-const %sto%s Bool)" % (get_letter(li),
					get_letter(lo))]

	# define top frequency "constraint"
	#smt += ["(assert %sto%s)" % (get_letter(top_in_text),
	#		get_letter(top_in_lang))]

	# define word constraints
	for word in set(words):
		word_formulas = []
		pattern = get_pattern(word)
		if not pattern in patterns:
			print("'%s' (%s) not in pattern db!" % (word, pattern))
			continue
		candidates = patterns[pattern]
		for candidate in candidates:
			word_formula = []
			for letter in word:
				literal = "%sto%s" % (get_letter(letter),
						get_letter(get_replacement(word,
							candidate, letter)))
				word_formula += [ literal ]
			f = "(and %s)" % " ".join(word_formula)

			word_formulas += [ f ]
		f = "(or %s)" % " ".join(word_formulas)
		smt += ["(assert %s)" % f]

	# one-hot requirement: one input to at most one output
	for li in input_letters:
		smt += [ "(assert %s)" % distinct([ "%sto%s" % \
				(get_letter(li), get_letter(lo)) \
				for lo in output_letters ]) ]

	# only one mapping per letter allowed (kill things like a->c & b->c)
	for lo in output_letters:
		smt += [ "(assert (=> (or %s) %s))" % (" ".join([ "%sto%s" % \
				(get_letter(li), get_letter(lo)) \
				for li in input_letters ]),
				distinct([ "%sto%s" % \
				(get_letter(li), get_letter(lo)) \
				for li in input_letters ])) ]

	#smt += ["(check-sat)", "(get-model)"]
	
	smt2 = "\n".join(smt)

	solver = z3.Solver()
	solver.reset()
	solver.add(z3.parse_smt2_string(smt2))
	result = solver.check()
	translations = []
	quality = {}
	n = 0
	while result == z3.sat:
		model = solver.model()
		decls = model.decls()
		mvars = { d.name(): d for d in decls }
		mappings = [ v for v in mvars if z3.is_true(model[mvars[v]]) ]
		get_from = lambda x: chr(int(x.split("to")[0][1:]))
		get_to = lambda x: chr(int(x.split("to")[1][1:]))
		trans = { get_from(m): get_to(m) for m in mappings }
		translations += [ trans ]

		t = "".join([ trans[c] if c in trans else c for c in text ])
		c = cost(t, lang_freq)
		quality[c] = trans

		n += 1
		if n >= iterations:
			break
		block = [ d() != model[d] for d in model ]
		solver.add(z3.Or(block))
		result = solver.check()

	if len(quality) < top:
		top = len(quality)
	best = sorted(quality.keys())[:top]
	return [ quality[i] for i in best ]
