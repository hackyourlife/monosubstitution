# -*- coding: utf-8 -*-
# vim:set ts=8 sts=8 sw=8 tw=80 noet cc=80:

import os
import re
import z3

frequencies_de = [ 6.516, 1.886, 2.732, 5.076, 16.396, 1.656, 3.009, 4.577,
		6.55, 0.268, 1.417, 3.437, 2.534, 9.776, 2.594, 0.67, 0.018,
		7.003, 7.27, 6.154, 4.166, 0.846, 1.921, 0.034, 0.039, 1.134]
frequencies_de_utf = { "ä": 0.578, "ö": 0.443, "ü": 0.995, "ß": 0.307 }

frequencies_en = [ 8.167, 1.492, 2.782, 4.253, 12.702, 2.228, 2.015, 6.094,
		6.966, 0.153, 0.772, 4.025, 2.406, 6.749, 7.507, 1.929, 0.095,
		5.987, 6.327, 9.056, 2.758, 0.978, 2.361, 0.15, 1.974, 0.074 ]
frequencies_es = [ 11.525, 2.215, 4.019, 5.01, 12.181, 0.692, 1.768, 0.703,
		6.247, 0.493, 0.011, 4.967, 3.157, 6.712, 8.683, 2.51, 0.877,
		6.871, 7.977, 4.632, 2.927, 1.138, 0.017, 0.215, 1.008, 0.467 ]
frequencies_es_utf = { "á": 0.502, "é": 0.433, "í": 0.725, "ñ": 0.311, "ó":
		0.827, "ú": 0.168, "ü": 0.012 }
frequencies_fr = [ 7.636, 0.901, 3.26, 3.669, 14.715, 1.066, 0.866, 0.737,
		7.529, 0.613, 0.049, 5.456, 2.968, 7.095, 5.796, 2.521, 1.362,
		6.693, 7.948, 7.244, 6.311, 1.838, 0.074, 0.427, 0.128, 0.326 ]
frequencies_fr_utf = { "à": 0.486, "â": 0.051, "œ": 0.018, "ç": 0.085, "è":
		0.271, "é": 1.504, "ê": 0.218, "ë": 0.008, "î": 0.045, "ï":
		0.005, "ô": 0.023, "ù": 0.058 }
frequencies_ru = { "А": 7.5, "Б": 2.01, "В": 4.33, "Г": 1.72, "Д": 3.09, "Е":
		8.5, "Ё": 0.2, "Ж": 1.01, "З": 1.48, "И": 7.09, "Й": 1.21, "К":
		3.3, "Л": 4.96, "М": 3.1, "Н": 6.7, "О": 11.07, "П": 2.47, "Р":
		4.33, "С": 4.97, "Т": 5.97, "У": 2.22, "Ф": 0.21, "Х": 0.95,
		"Ц": 0.39, "Ч": 1.4, "Ш": 0.72, "Щ": 0.3, "Ъ": 0.02, "Ы": 2.36,
		"Ь": 1.84, "Э": 0.36, "Ю": 0.47, "Я": 1.96 }

dict_paths = {
		"es": "/usr/share/dict/spanish",
		"fr": "/usr/share/dict/french",
		"ru": "russian.dic",
		"en": "/usr/share/dict/british-english",
		"de": "/usr/share/dict/german",
		"de-small": "german-small.dic"
		}

if not os.path.exists(dict_paths["de"]):
	dict_paths["de"] = "/usr/share/dict/ngerman"

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
	if lang in [ "de", "de-small", "de-medium" ]:
		return merge_dicts(basic_frequencies(frequencies_de),
				scale(frequencies_de_utf))
	if lang == "es":
		return merge_dicts(basic_frequencies(frequencies_es),
				scale(frequencies_es_utf))
	if lang == "fr":
		return merge_dicts(basic_frequencies(frequencies_fr),
				scale(frequencies_fr_utf))
	if lang == "ru":
		return scale(frequencies_ru)
	raise ValueError("no frequency table for language \"%s\"" % lang)

dicts = {}
def _read(path):
	print("loading %s" % path)
	with open(path) as f:
		return [ l.strip().lower() for l in f.readlines() \
				if len(l.strip()) > 0 ]

def _get_dict(lang):
	if lang == "de":
		return set(_read(dict_paths[lang]) +
				_read("german.dic"))
	elif lang == "de-medium":
		return set(_read(dict_paths["de"]))
	elif lang in dict_paths:
		return set(_read(dict_paths[lang]))
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
			pattern_dicts[lang][p].add(w)
		else:
			pattern_dicts[lang][p] = set([ w ])
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

	def encode_word(w):
		return "".join([ get_letter(l) for l in w ])

	smt = []
	# define variables
	for li in input_letters:
		for lo in output_letters:
			smt += ["(declare-const %sto%s Bool)" % (get_letter(li),
					get_letter(lo))]

	# unknown words
	for w in set(words):
		smt += ["(declare-const no-%s Bool)" % encode_word(w)]

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
		word_formulas += [ "no-%s" % encode_word(word) ]
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

	# allow no unknown words initially
	smt += ["(assert (and %s))" % " ".join([ "(not no-%s)" % encode_word(w)\
			for w in set(words) ])]

	#smt += ["(check-sat)", "(get-model)"]

	smt2 = "\n".join(smt)

	solver = z3.Solver()
	solver.reset()
	solver.add(z3.parse_smt2_string(smt2))
	result = solver.check()
	translations = []
	quality = {}
	n = 0

	# allow one unknown word, if it is unsat otherwise
	if result != z3.sat:
		smt[-1] = "(assert %s)" % distinct([ "no-%s" % encode_word(w) \
				for w in set(words)])
		smt2 = "\n".join(smt)
		solver.reset()
		solver.add(z3.parse_smt2_string(smt2))
		result = solver.check()

	while result == z3.sat:
		model = solver.model()
		decls = model.decls()
		mvars = { d.name(): d for d in decls }
		mappings = [ v for v in mvars if z3.is_true(model[mvars[v]]) ]
		get_from = lambda x: chr(int(x.split("to")[0][1:]))
		get_to = lambda x: chr(int(x.split("to")[1][1:]))
		trans = { get_from(m): get_to(m) for m in mappings \
				if not m.startswith("no-") }
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

def crack_tree(text, lang, skip_same=True):
	text = text.lower()

	d = get_dict(lang)
	patterns = get_pattern_dict(lang)
	words = get_words(text)
	unique_words = set(words)

	alphabet = sorted(list(set("".join(unique_words))))

	lang_freq = default_frequencies(lang)

	word_list = { word: sorted(patterns[get_pattern(word)]) \
			for word in unique_words \
			if get_pattern(word) in patterns }

	count = lambda a, b: len(set(a)) + len(set(b)) - len(set(a + b))

	def find_common(found, new):
		return list(reversed(sorted(new, key=lambda x: count(found, x) \
				* len(patterns[get_pattern(x)]))))

	def heuristic(word_list):
		tree_starts = sorted(word_list.keys(),
				key=lambda x: -len(set(x)) / len(word_list[x]))
		print([ "%s: %s" % (w, len(word_list[w])) for w in tree_starts ])

		words = word_list.keys()
		result = [ tree_starts[0] ]
		rest = tree_starts[1:]
		joined = result[0]
		while len(rest) > 0:
			s = find_common(joined, rest)
			result += [ s[0] ]
			rest = s[1:]
			joined = "".join(set(joined + s[0]))
		return result

	_words = heuristic(word_list)
	Dmax = len(word_list)

	print(_words)
	print([ "".join(sorted(list(set(w)))) for w in _words ])
	print("Dmax = %d, len(unique_words) = %d" % (Dmax, len(unique_words)))

	mappings = {}
	best_score = 0

	class Finished(Exception):
		pass

	def translate(text, trans):
		def _trans(c, trans):
			l = c.lower()
			if l in trans:
				return trans[l] if l == c else trans[l].upper()
			return c
		return "".join([ _trans(c, trans) for c in text ])

	def get_mapping(f):
		return "%s -> %s" % ("".join(alphabet),
				"".join([ f[l] if l in f else "*" \
						for l in alphabet ]))

	def compare_score(f, score):
		nonlocal best_score, mappings
		if score >= best_score:
			print("%s: %s (%s)" % (score, get_mapping(f),
				translate(text, f)))
			if score in mappings:
				mappings[score] += [ f ]
			else:
				mappings[score] = [ f ]
			best_score = score

	def can_get_better(depth, score):
		nonlocal best_score, Dmax
		return Dmax - depth + score >= best_score

	def consistent(f, W, X):
		f_new = { k: v for (k, v) in f.items() }
		g = set(f.values())
		for i in range(len(W)):
			c = W[i]
			if c in f_new:
				if f_new[c] != X[i]:
					return False, f
			elif skip_same and X[i] in g:
				return False, f
			f_new[c] = X[i]
			g.add(X[i])
		return True, f_new

	def solve(depth, f, score):
		if depth >= Dmax:
			compare_score(f, score)
			#if score == depth:
			#	raise Finished()
			return
		elif not can_get_better(depth, score):
			return
		else:
			w = _words[depth]
			for x in word_list[w]:
				c, f_new = consistent(f, w, x)
				if c:
					solve(depth + 1, f_new, score + 1)
			solve(depth + 1, f, score)

	try:
		solve(0, {}, 0)
	except Finished:
		pass

	return sorted(mappings[best_score], key=lambda x:
			cost(translate(text, x), lang_freq))
