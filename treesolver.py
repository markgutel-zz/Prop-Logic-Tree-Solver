# function to ask user for input of one or more premises and an optional conclusion
# this function will automatically negate the conclusion
#
# run this without any arguments, it will promt the user for and output a list of sentences
# as they are entered, it strips white space from the input string,
# uses syntax_checker to test input strings and will prompt to reenter until
# syntax_checker returns 'wff' for that string.
#
# depends on syntax_checker - should be compatable with any logic as long as syntax_checker
# will call each input a 'wff'

def get_input_list():
    
    input_list = []

    input_str = str(raw_input('Enter your first premise: '))
    nowhitespc = input_str.replace(' ', '')
    print nowhitespc
    while syntax_checker(nowhitespc) == 'syntax' or syntax_hints(nowhitespc) == 'syntax':
        input_str = str(raw_input('Please correct and reenter your first premise: '))
        nowhitespc = input_str.replace(' ', '')
        print nowhitespc
    input_list.append(nowhitespc)
        
    a = 0
    while (a == 0):
        input_str = str(raw_input('Enter another premise. Hit Enter if none.: '))
        if (input_str != ''):
            nowhitespc1 = input_str.replace(' ', '')
            print nowhitespc1
            while syntax_checker(nowhitespc1) == 'syntax' or syntax_hints(nowhitespc1) == 'syntax':
                print syntax_hints(nowhitespc1)
                input_str = str(raw_input('Please correct and reenter your last premise: '))
                nowhitespc1 = input_str.replace(' ', '')
                print nowhitespc1
            input_list.append(nowhitespc1)
            a = 0
        else:
            a = 1

    input_str = str(raw_input('Enter any conclusion. Hit Enter if none.: '))
    if (input_str != ''):
        nowhitespc2 = input_str.replace(' ','')
        while syntax_checker(nowhitespc2) == 'syntax' or syntax_hints(nowhitespc2) == 'syntax':
            input_str = str(raw_input('Please correct and reenter your conclusion: '))
            nowhitespc2 = input_str.replace(' ', '')
            print nowhitespc2
        negated_str = '~' + nowhitespc2
        print negated_str
        input_list.append(negated_str)

    return input_list


# this is a syntax checker, depends on main_con, and atomic_test


# syntax checker, maybe technique, when see "~", make sure it is followed by ~, atomic, or (
# for quantifiers, check that each bound variable is used at least once
# for con, make sure followed by, quantifier, atomic, ~,


# syntax_checker depends on atomic_test and main_con
# how reliable is it, how does that depend on the reliability of atomic and main_con?
# if atomic is always reliable, main_con doesn't have to be
# as of now, 8/1/18, atomic only finds prop logic atomics, when upgrading, need to ensure it works
# We run syntax_checker in a loop that ends either with all decomposed pieces found atomic
# or when we compare the input and output of syntax_checker and they are identical
# if main_con makes an error, eventually atomic will halt with an error.

# syntax_checker runs a while loop until the working list is empty or exits for a syntax error
#
# so, if it gets input an empty string, it will return 'wff'


# checks syntax of propositional logic sentences - returns 'wff' or 'syntax'
#
# depends on main_con and atomic_test, assumes all white space removed from input sentence
#
# if implement a function to distribute quantifiers, as described below, then
# this would be relatively robust and compatible with predicate logic
# if wanted to support modal logic, would probably need a modal stripping function



def syntax_checker(sentence):

    worklist = []
    worklist.append(sentence)            
    while worklist != []:

        testsen = worklist.pop()
        atom = atomic_test(testsen)        
        if atom == 'atomic':
            return 'wff'
        elif atom == 'non-atomic':
            work2list = []
            work2list = main_con(testsen)
            if work2list != []:
                errorcheck = work2list.pop(0)
                if errorcheck == 'syntax-composite':
                    print sentence,'has a syntax error.',testsen,'has no main connective.'
                    return 'syntax'
                worklist.append(errorcheck)
                if work2list != []:
                    worklist.append(work2list.pop(0))
                else:
                    print 'Something strange happened. Main_con returned an empty Rightsen.'
                    return 'syntax'
            else:
                print 'Something strange happened. Main_con returned an empty list.'
                return 'syntax'
        elif atom == 'syntax-atomic':
            print sentence,'has a syntax error.',testsen,'is not a well formed atomic sentence.'
            return 'syntax'
        else:
            print 'Something strange happened. Atomic_test returned None.'
            return 'syntax'
    return worklist


# predicate logic syntax checker idea: distribute the quantifiers to the atomic senteces that have
# those varaibles. It would make the predicate logic verision of atomic_test easier, would be
# easier to tell all the variables were bound.
#
# this would make syntax_checker robust, as long as the quantifiers are distributed
# might need to apply quantifier negation first


# draft syntax checker that missed some cases. Repurposing into giving a second error message for
# most sentences with syntax errors.
# assumes the input sentence is non-atomic

def syntax_hints(sentence):

    pos_sentence = neg_stripper(sentence)

    if atomic_test(sentence) == 'atomic':
        return 'atomic'
    
    elif pos_sentence[0] == '(':
        if pos_sentence[len(pos_sentence)-1] == ')':

            leftpar = pos_sentence.count('(')
            rightpar = pos_sentence.count(')')
            connect = pos_sentence.count('&') + pos_sentence.count('v') + pos_sentence.count('>')
                    
            if leftpar == rightpar:
                if leftpar == connect:
                    s = 0
                    while s < len(pos_sentence):
                        if pos_sentence[s] == '&' or pos_sentence[s] == 'v' or pos_sentence[s] == '>':
                            leftsen = pos_sentence[0:s]
                            rightsen = pos_sentence[s+1:len(pos_sentence)]

                            leftsen = leftsen[leftsen.rfind('(')+1:len(leftsen)]
                            rightsen = rightsen[0:rightsen.find(')')]
                            negrightsen = neg_stripper(rightsen)
                            if rightsen != '':
                                if negrightsen[0] != '~':      
                                    if leftsen != '':
                                        if leftsen[len(leftsen)-1] == ')' or atomic_test(leftsen) == 'atomic': 
                                            if negrightsen[0] != '(' and atomic_test(negrightsen) != 'atomic':    
                                                print sentence,'has a syntax error. Either',negrightsen[0],'should be ( or ',rightsen,'should be an atomic sentence.'
                                                return 'syntax'
                                            else:
                                                print ' '
                                                return 'cool?'
                                        else:
                                            print sentence,'has a syntax error. Either',leftsen[len(leftsen)-1],'should be ) or ',leftsen,'should be an atomic sentence.'
                                            return 'syntax'

                                    else: 
                                        print sentence,'has a syntax error. ',sentence[s],' may have a missing left sentence'
                                        return 'syntax'
                                else:
                                    print sentence,'has a syntax error. ',rightsen,'has some negation errors.'
                                    return 'syntax'
                            else:
                                print sentence,'has a syntax error. ',sentence[s],' may have a missing right sentence'
                                return 'syntax'
                        s = s + 1
                else:
                    print sentence,'has a syntax error. There are',leftpar,'sets of parentheses, but ',connect,'connectives.'
                    return 'syntax'
            else:
                print sentence,'has a syntax error. It has ',leftpar,'( and ',rightpar,' )'
                return 'syntax'
        else:
            print sentence,'has a syntax error. It has a trailing',sentence[len(sentence)-1]
            return 'syntax'
    else:
        print sentence,'has a syntax error. It is missing a ( near the beginning or has a ~ at the end.'
        return 'syntax'

# function to check for any pairs of strings in a list for the form A, ~A
#
# no dependencies, very robust, should be compatible with any logic

def consistency(input_list):
    
    for sentence in input_list:
        if sentence[0] == '~':
            pos_sentence = sentence[1:len(sentence)]
            for sentence1 in input_list:
                if pos_sentence == sentence1:
                    input_list.append('x')
    return input_list

def check_consistency(listin):

    worklist = listin[:]
    worklist = consistency(worklist)
    if worklist != []:
        xcheck = worklist.pop()
    
        if xcheck == 'x':
            return 'valid'
        else:
            return 'invalid'
    else:
        print 'error'
        return 'error'
    

# function to remove finished lists from a list of lists. finished lists are either inconsistent or entirely atomic
#
# outputs a two item list, first is the list of non-finshied lists of sentences
# the second item, is the list of lists of found inconsistent lists of sentences. May be empty
#
# depends on atomic_list. does not explicitly depend on consistency() but is searching for 'x's that
# consistency() appends to inconsistent lists
#
# could just check pop() of each list to check for x, but the currect search for x anywhere in the list
# seems more robust. Surely there is a single function to search a list for a particular string

def rm_finshed_lists(listoflistsin):

    listoflistsSout = []
    listoflistskeep = []
    listoflistsrm = []
    a = 0

    for list in listoflistsin:
        if atomic_list(list) != 'atomic-list':
            for sentence in list:
                if sentence != 'x':
                    a = a
                elif sentence == 'x':
                    a = a + 1
                else:
                    print 'error'
                    return 'error'
        else:
            listoflistsrm.append(list)

        if a <= 0:
            listoflistskeep.append(list)
        else:
            listoflistsrm.append(list)

    listoflistsSout.append(listoflistskeep)
    listoflistsSout.append(listoflistsrm)

    return listoflistsSout

            

# function to apply double negation elimination to all sentences in list
#
# no dependencies, should be robust and compatible with any logic

def doubleneg(input_list):
    output_list = []
    for sentence in input_list:
        a = 0
        while a < 1:
            if sentence[0:2] == '~~':
                sentence = sentence[2:len(sentence)]
                a = 0
            else:
                a = 1
        output_list.append(sentence)
    return output_list

# function to strip leading ~'s from sentence and return it
#
# no dependencies, should be robust and compatible with any logic
# used by atomic_test, at least up through the prop logic version

def neg_stripper(sentence):
    if sentence[len(sentence)-1] != '~':
        while sentence[0] == '~':
            sentence = sentence[1:len(sentence)]
    return sentence



# testing for propositional atomic sentences
# returns 'atomic' for an atomic sentence
# returns 'non-atomic' for possible composite sentences
# returns 'syntax' for just one test, two letters next to one another
#
# depends on neg_stripper - will need a lot of work to make compatable with
# predicate logic etc.

def atomic_test(sentence):
    if sentence.count('(') + sentence.count(')') + sentence.count('&') + sentence.count('v') + sentence.count('>') > 0:
        return 'non-atomic'
    elif sentence == '':
        return 'syntax-atomic'
    else:
        sentence = neg_stripper(sentence)
        if sentence[0] == '~':
            return 'syntax-atomic'
        elif len(sentence) > 1:
            return 'syntax-atomic'
        else:
            return 'atomic'

def atomic_list(listin):
    a = 0
    for sentence in listin:
        if atomic_test(sentence) == 'non-atomic':
            a = a + 1
        elif atomic_test(sentence) == 'syntax-atomic':
            print 'syntax'
            return 'syntax'
    if a > 0:
        return 'composite-list'
    else:
        return 'atomic-list'

def atomic_listSQ(listoflistsin):
    
    a = 0
    for list in listoflistsin:
        atomlist = atomic_list(list)
        
        if atomlist == 'composite-list':
            a = a + 1
        elif atomlist == 'atomic-list':
            a = a
        else:
            print 'error'
            return 'error'
    if a > 0:
        return 'composite-listSQ'
    else:
        return 'atomic-listSQ'

# function to test sentences for 'atomic', or if the main connective is 'branch' or 'nbranch'
#
# depends on main_con and atomic_test


def branch_test(sentence):

    atomtest = atomic_test(sentence)

    if atomtest == 'non-atomic':

        testlist = main_con(sentence)
        test = testlist.pop()
    
        if test == '~':
        
            pen = testlist.pop()
        
            if pen == '&':
                return 'branch'

            elif pen == 'v' or pen == '>':
                return 'nbranch'
            else:
                print 'error'
                return 'error'
        
        elif test == 'v' or test == '>':
            return 'branch'

        elif test == '&':
            return 'nbranch'

        else:
            print 'error'
            return 'error'

    elif atomtest == 'atomic':
        return 'atomic'
    else:
        print 'error'
        return 'error'

def nbranch_list(listin):
    a = 0
    for sentence in listin:
        
        branchtest = branch_test(sentence)
        
        if branchtest == 'nbranch':
            a = a + 1
        elif branchtest == 'branch' or branchtest == 'atomic':
            a = a
        else:
            print 'error'
            return 'error'
    if a > 0:
        return 'nbranch-list'
    else:
        return 'branch-list'

def nbranch_listSQ(listoflistsin):
    a = 0
    for list in listoflistsin:
        
        nbranchlisttest = nbranch_list(list)
        
        if nbranchlisttest == 'nbranch-list':
            a = a + 1
        elif nbranchlisttest == 'branch-list':
            a = a
        else:
            print 'error'
            return 'error'
    if a > 0:
        return 'nbranch-listSQ'
    else:
        return 'branch-listSQ'


        
# finds the main connective in a prop logic sentence
#
# input is one sentence - output is a 3 or 4 item list [Left side, Right side, Main Connective, Any negation]
# if it fails to find the connective, it will output a single item error list ['syntax-composite']
#
# does not explicitly depend on atomic_test being run first, but it probably should be
#
# either it will fail with an error, or it will take out a connective and return the two
# remaining sides of the sentence. If those sides do not have any connectives, either atomic_test
# will return an error. Or, eventaully, there won't be any more connectives, and main_con will
# return an error. So main_con can give false positives, and syntax_checker will still be
# relable.
#
# it also strips off the two outermost symbols on each round


def main_con(sentence):
    listout = []
    s = 0
    while (s < len(sentence)):
        if (sentence[s] == '&' or sentence[s] == 'v' or sentence[s] == '>'):
            if sentence[s-1] != '(' and sentence[s+1] != ')':
                leftsen = sentence[sentence.find('(')+1:s]
                rightsen = sentence[s+1:len(sentence)-1]
                if sentence.count('(') >= 1 and leftsen.count('(') == leftsen.count(')') and rightsen.count('(') == rightsen.count(')'):
                    listout.append(leftsen)
                    listout.append(rightsen)
                    listout.append(sentence[s])
                    if sentence[0] == '~':
                        listout.append('~')
                    return listout
        s = s + 1
    listout.append('syntax-composite')
    return listout

# this applies any non-branching rules to the output of main_con
#
# doesn't explicitly depend on any other functions
# BUT, it is designed to take as input, a list from main_con
# that list will be, in order [left side,right side, main connective, negation if any]
#
# it should be robust, then, and compatible with any logic


def nbranch(listin):
    listout = []
    last = listin.pop()
    if last == '&':
        listout.append(listin.pop(0))
        listout.append(listin.pop())
    elif last == '~':
        pen = listin.pop()
        if pen == '>':
            listout.append(listin.pop(0))               
            listout.append('~' + listin.pop())
        elif pen == 'v':
            listout.append('~' + listin.pop(0))
            listout.append('~' + listin.pop())
        else:
            listout.append(listin.pop(0))
            listout.append(listin.pop())
            listout.append(pen)
            listout.append('~')
    elif last == '>' or last == 'v':
            listout.append(listin.pop(0))
            listout.append(listin.pop())
            listout.append(last)
    else:
        listout.append(listin.pop(0))
        listout.append(last)
    return listout


def nbranch_apply(listin):
    
    while nbranch_list(listin) == 'nbranch':
        testsen = listin.pop(0)
        branchtest = branch_test(testsen)
        
        if branchtest == 'branch' or branchtest == 'atomic':
            listin.append(testsen)
        elif branchtest == 'nbranch':

            listin.extend(doubleneg(nbranch(main_con(doubleneg(testsen)))))

            print testsen,'is non-branching.'
        else:
            print 'error'
            return 'error'
    return listin







# branch function, applies branching rules to output list of main_con, outputs two item list of leftsen and rightsen
#
# 

def branch(listin):
    listout = []
    last = listin.pop()
    if last == 'v':
        listout.append(listin.pop(0))
        listout.append(listin.pop())
    elif last == '>':
        listout.append('~' + listin.pop(0))
        listout.append(listin.pop())
    elif last == '~':
        pen = listin.pop()
        if pen == '&':
            listout.append('~' + listin.pop(0))               
            listout.append('~' + listin.pop())
        else:
            listout.append(listin.pop(0))
            listout.append(listin.pop())
            listout.append(pen)
            listout.append('~')
    elif last == '&':
            listout.append(listin.pop(0))
            listout.append(listin.pop())
            listout.append(last)
    else:
        listout.append(listin.pop(0))
        listout.append(last)
    return listout

# function to apply the branching rule to an input list and output a list of 


def branch_apply(listin):

    listoflistsout = []
    listoflistsout.append(listin)

    while nbranch_listSQ(listoflistsout) != 'nbranch-listSQ' and atomic_listSQ(listoflistsout) != 'atomic':

        testlist = listoflistsout.pop(0)
        atomlist = atomic_list(testlist)
                                                                               
        while nbranch_list(testlist) != 'nbranch-list' and atomic_list(testlist) != 'atomic-list':
                                                                               
            sentence = testlist.pop(0)
            atomtest = atomic_test(sentence)
        
            if atomtest == 'non-atomic':
                                                                               
                if branch_test(sentence) == 'branch':

                    list1 = testlist[:]
                    list2 = testlist[:]
                    worklist = doubleneg(branch(main_con(sentence)))
                    list1.append(worklist.pop())
                    list2.append(worklist.pop())

                    listoflistsout.append(list1)
                    listoflistsout.append(list1)
                        
                else:
                    print 'error'
                    return 'error'
                    
            elif atomtest == 'atomic':
                testlist.append(sentence)

            else:
                print 'error'
                return 'error'                                                                 

    return listoflistsout



######################
# The Actual Program #
######################


listin = get_input_list()


listoffinishedlists = []
worklistoflists = []

worklist = listin[:]

worklistoflists.append(worklist)

while worklistoflists != []:

    print worklistoflists
    
    for list in worklistoflists:

        print list
        
        list = doubleneg(nbranch_apply(list))

        print list
        
        list = consistency(list)

        print list
        
    templistSQ = rm_finshed_lists(worklistoflists)

    print templistSQ
    
    removedlistSQ = templistSQ.pop()
    keptlistSQ = templistSQ.pop()
    
    if removedlistSQ != []:
        listoffinishedlists.extend(removedlistSQ)
    worklistoflists = []
    worklistoflists.extend(keptlistSQ)

    if worklistoflists != []:
        worklist = worklistoflists.pop(0)
        worklistoflists.extend(doubleneg(branch_apply(worklist)))


a = 0
for list in listoffinishedlists:
    concheck = check_consistency(list)
    if concheck == 'invalid':
        print list,'is consistent.'
        a = a + 1
    elif concheck == 'valid':
        a = a
    else:
        print 'error'
        end
if a > 0:
    print listin,'is a consistent list of sentences. If you entered an argument, it is invalid.'
else:
    print listin,'is an inconsistent list of sentences. If you entered an argument, it is valid.'












# Version 0.1 of prop logic tree solver finished 2:15pm 8/10/18 - not working yet
# need to test: rm_finshed_listoflists, atomic_listoflists, nbranch_apply, branch_apply








