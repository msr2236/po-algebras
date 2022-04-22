# Signature for input and output (the LaTeX symbols can be changed to agree with other conventions)

from IPython.display import display, Math
#from provers import *
import time

FOLang = { #Constant operation symbols
"c":(0,"c"), "d":(0,"d"), "e":(0,"e"), "0":(0,"zero"), "1":(0,"one"), "\\bot":(0,"bot"), "\\top":(0,"top"),
#Logical connectives 
"\\iff":(1,"=="," <-> "), "\\implies":(2,"<="," -> "), "\\text{ or }":(3," or ","|"), "\\text{ and }":(4," and ","&"), "\\neg":(5," not "),
# Quantifiers
"\\forall":(6," all","all "), "\\exists":(6," any","exists "),
# Infix relation symbols
"\\le":(7,"le","<="), "\\ge":(7,"ge",">="), "=":(7,"=="), "\\ne":(7,"!=","!="),
# Infix operation symbols
"\\to":(8,"to","->"), "\\leftarrow":(8,"leftarrow"), "\\vee":(9,"j"," v "), "\\wedge":(9,"m","^"),
"+":(10,"p"), "\\oplus":(10,"oplus"), "\\ominus":(10,"ominus"), "/":(11,"rd"), "\\backslash":(11,"ld"),
"\\cdot":(12,"cdot"), "\\circ":(12,"circ"), "\\odot":(12,"odot"), "*":(12,"t"),
#Prefix unary operation symbols
"f":(13,"f"), "g":(13,"g"), "\\sim":(13,"sim","~"), "-":(13,"minus"), "\\diamond":(13,"dia","dia"), "\\box":(13,"box"),
#Postfix unary operation symbols
"^*":(14,"star"), "^{-1}":(14,"inv","inv"), "\\smallsmile":(14,"conv","conv"), "'":(14,"pr")
}
Vars = ["x","y","z","u","v","w"]
for v in Vars: FOLang.update({(v if i==10 else v+"_"+str(i)):(0,) for i in range(11)})

# Constant operation symbols
Cons="c"; Cond="d"; Iden="1"; Zero="0"; Bot="\\bot"; Top="\\top"

# Prefix unary operation symbols
Fop="f"; Gop="g"; Lneg="\\sim"; Rneg="-"; Dia="\\diamond"; Box="\\box"; Rtri="\\vartriangleright"; Ltri="\\vartriangleleft"

# Postfix unary operation symbols
Star="^*"; Inv="^{-1}"; Conv="\\smallsmile"; Pri="'"

# Infix binary operation symbols
Meet="\\wedge"; Join="\\vee"; Mult="\\cdot"; Lres="/"; Rres="\\backslash"; Omult="\\odot"; Smul="*";
Add="+"; Oadd="\\oplus"; Comp="\\circ"; Rimp="\\to"; Limp="\\leftarrow"; Ominus="\\ominus"; triR="\\triangleright"; triL="\\triangleleft"

# Infix binary relation symbols
Le="\\le"; Ge="\\ge"; Eq="="; Neq="\\ne"

# First-order logic connectives and quantifiers
And="\\text{ and }"; Or="\\text{ or }"; Imp="\\implies"; Not="\\neg"; Iff="\\iff"; All="\\forall"; Exists="\\exists"

VAR = set(["u","v","w","x","y","z"])|set("x_"+str(i) for i in range(10))|set("y_"+str(i) for i in range(10))
CONST = set([Cons,Cond,Iden,Zero,Bot,Top])
PREFIX = [(Fop,11),(Gop,11),(Lneg,11),(Rneg,11),(Dia,11),(Box,11),(Rtri,11),(Ltri,11),(Not,5)] # (symbol, precedence)
POSTFIX = [(Star,12),(Inv,12),(Conv,12),(Pri,12)]
INFIX = [(Mult,10),(Omult,10),(Comp,10),(Rres,9),(Lres,9),(triR,9),(triL,9),(Add,8),(Oadd,8),(Ominus,8),(Meet,7),(Join,7),
         (Rimp,6),(Limp,6),(Le,5),(Eq,5),(Neq,5),(And,4),(Or,4),(Imp,3),(Iff,2)]
QUANT = [(All,5),(Exists,5)]

# can add further \newcommand macros in the string below
Macros=""  #r"\newcommand{\coimp}{-\!\raisebox{.5pt}{\scriptsize<}\,}"

pysym={"u":"u","v":"v","w":"w","x":"x","y":"y","z":"z","c":"c","d":"d","1":"1","0":"0","\\bot":"b","\\top":"t","f":"f","g":"g",
       "\\sim":"sim","-":"mi","\\diamond":"dd","\\box":"bx","\\triangleright":"tr","\\triangleleft":"tl","\\vartriangleright":"vtr","\\vartriangleleft":"vtl",
       "^*":"star","^{-1}":"i","\\smallsmile":"conv","'":"c","\\wedge":"mt","\\vee":"jn","\\cdot":"cd","/":"rd","\\backslash":"ld",
       "\\odot":"odot","*":"m","+":"j","\\oplus":"op","\\ominus":"om","\\circ":"ci","\\to":"to","\\leftarrow":"ri",
       "\\le":"le","\\ge":"ge","=":"==","\\ne":"!=","\\text{ and }":" and ","\\text{ or }":" or ",
       "\\implies":" <= ","\\iff":" == ","\\forall":"all","\\exists":"any"}

p9sym={"u":"u","v":"v","w":"w","x":"x","y":"y","z":"z","c":"c","d":"d","1":"1","0":"0","\\bot":"b","\\top":"t","f":"f","g":"g",
       "\\sim":"~","-":"-","\\diamond":"dd","\\box":"bx","\\triangleright":" r ","\\triangleleft":" t ","\\vartriangleright":"tr","\\vartriangleleft":"tl",
       "^*":"'","^{-1}":"i","\\smallsmile":"'","'":"'","\\wedge":"^","\\vee":" v ","\\cdot":"*","/":"/","\\backslash":"\ ",
       "\\odot":"*","*":"*","+":"+","\\oplus":"+","\\ominus":"<-","\\circ":"*","\\to":"->","\\leftarrow":"<-",
       "\\le":"<=","\\ge":">=","=":"=","\\ne":"!=","\\text{ and }":" & ","\\text{ or }":" | ",
       "\\implies":" -> ","\\iff":" <-> ","\\forall":"all","\\exists":"exists"}

opts=["op(700,infix,\"r\")","op(700,infix,\"t\")"]

################## Parser code (can ignore this) #################
# Terms are read using Vaughn Pratt's top-down parsing algorithm #

symbol_table = {}

def wrap(subt, t): # decide when to add parentheses during printing of terms
    return subt.tex() if subt.lbp > t.lbp or len(subt.a)<=1 else "("+subt.tex()+")"

class symbol_base(object):
    a = []
    def __repr__(self): 
        return self.tex()
    def tex(self):
        if len(self.a) == 0: return self.id
        if len(self.a) == 1: 
          if self.id[0]=="^": return wrap(self.a[0],self)+self.id
          return self.id+" "+wrap(self.a[0],self)
        if len(self.a) == 2: 
          return wrap(self.a[0],self)+self.id+(" " if self.id[0]=='\\' else "")+wrap(self.a[1],self)
        return self.id+" "+self.a[0].id+self.a[1].id+self.a[2].id

def symbol(id, bp=0): # identifier, binding power
    if id in symbol_table:
        s = symbol_table[id]    # look symbol up in table
        s.lbp = max(bp, s.lbp)  # update left binding power
    else:
        class s(symbol_base):   # create class for this symbol
            pass
        s.id = id
        s.lbp = bp
        s.nulld = lambda self: self
        symbol_table[id] = s
    return s

def advance(id=None):
    global token
    if id and token.id != id:
        raise SyntaxError("Expected "+id+" got "+token.id)
    token = next()

def nulld(self): # null denotation
    expr = expression()
    advance(")")
    return expr

def infix(id, bp):
    def leftd(self, left): # left denotation
        self.a = [left]
        self.a.append(expression(bp))
        return self
    symbol(id, bp).leftd = leftd

def prefix(id, bp):
    global token
    def nulld(self): # null denotation
        global token
        if token.id != "(":
            self.a = [expression(bp)]
            return self
        else:
            token = next()
            self.a = []
            if token.id != ")":
                while 1:
                    self.a.append(expression())
                    if token.id != ",":
                        break
                    advance(",")
            advance(")")
            return self
    symbol(id, bp).nulld = nulld

def postfix(id, bp):
    def leftd(self,left): # left denotation
        self.a = [left]
        return self
    symbol(id, bp).leftd = leftd

symbol("(").nulld = nulld
symbol(")")
symbol("[").nulld = nulld
symbol("]")
symbol("(end)")

for s in FOLang.keys():
    if FOLang[s][0]==0: symbol(s)
    elif FOLang[s][0]<=5: infix(s,FOLang[s][0])
    elif FOLang[s][0]<=6:
        for v in Vars:
            prefix(s+" "+v,FOLang[s][0])
            for i in range(10):
                prefix(s+" "+v+"_"+str(i),FOLang[s][0])
    elif FOLang[s][0]<=12: infix(s,FOLang[s][0])
    elif FOLang[s][0]<=13: prefix(s,FOLang[s][0])
    elif FOLang[s][0]<=14: postfix(s,FOLang[s][0])

def tokenize(st):
    i = 0
    while i<len(st):
        tok = st[i] #read single-letter token
        j = i+1
        if j<len(st) and st[j]=="_": #read subscript
            j+=1
            if st[j]=="{": j+=1
            while j<len(st) and st[j]>='0' and st[j]<='9': j+=1
            if j<len(st) and st[j]=="}": j+=1
            tok = st[i:j]
        elif j<len(st) and st[i]=="^": #read postfix superscript operation
            if st[j]=="{": j+=1
            if st[j]=="-" or st[j]=="*" or st[j]=="\\": j+=1
            if st[j]=="1": j+=1
            if st[j-1]=='\\':
                while j<len(st) and ((st[j]>='a' and st[j]<='z') or (st[j]>='A' and st[j]<='Z')): j+=1
            if j<len(st) and st[j]=="}": j+=1
            tok = st[i:j]
        elif tok=="{":
            tok = st[j]
            j+=1
        if tok=="\\": #read Latex symbol
            while j<len(st) and ((st[j]>='a' and st[j]<='z') or (st[j]>='A' and st[j]<='Z')): j+=1
            if st[i]=="{" and st[j]=="}": j+=1
            tok = st[i:j]
            if tok in ["\\mathbf","\\forall","\\exists"]:
              j+=2
              if j<len(st) and st[j]=="_": #read subscript
                j+=1
                if st[j]=="{": j+=1
                while j<len(st) and st[j]>='0' and st[j]<='9': j+=1
                if j<len(st) and st[j]=="}": j+=1
              tok = st[i:j]
            elif tok=="\\text":
              j+=2
              while j<len(st) and st[j]>='a' and st[j]<='z': j+=1
              j+=1
              if j<len(st) and st[j]=="}": j+=1
              tok = st[i:j]
        i = j
        if tok!=' ':
            symb = symbol_table[tok]
            if not symb: raise SyntaxError("Unknown operator")
            yield symb()
    symb = symbol_table["(end)"]
    yield symb()

def expression(rbp=0):
    global token
    t = token
    token = next()
    left = t.nulld()
    while rbp < token.lbp:
        t = token
        token = next()
        left = t.leftd(left)
    return left

def parse(str): # e.g., t = parse(r"(p\circ q)\lor \mathbf t")
    global token, next
    next = tokenize(str.replace("{\\sim}","\\sim ").replace("{-}","-")).__next__
    token = next()
    return expression()

def showformula(A, info=True): # display a (list of) formula(s)
  st = A if type(A)==str else repr(A)
  if info==True: display(Math(Macros+st))

########### end of parser #####################################

def formulavars(A):
  if A.a==[]: return set([A.id] if A.id in Vars else [])
  if len(A.a)==1: return formulavars(A.a[0])
  return formulavars(A.a[0]) | formulavars(A.a[1])

def pythonout(A): #output formula A in python format
  symbs = ["=","\\implies","\\iff","\\text{ and }","\\text{ or }"]
  if A.a==[]: return pysym[A.id]
  if len(A.a)==1: return pysym[A.id]+"["+pythonout(A.a[0])+"]"
  if A.id in symbs:
    st0 = "("+pythonout(A.a[0])+")" if A.a[0].id in symbs else pythonout(A.a[0])
    st1 = "("+pythonout(A.a[1])+")" if A.a[1].id in symbs else pythonout(A.a[1])
    return st0+pysym[A.id]+st1
  if A.id == "\\le": return "j["+pythonout(A.a[0])+"]["+pythonout(A.a[1])+"]=="+pythonout(A.a[1])
  if A.id == "\\ge": return "j["+pythonout(A.a[0])+"]["+pythonout(A.a[1])+"]=="+pythonout(A.a[0])
  return pysym[A.id]+"["+pythonout(A.a[0])+"]["+pythonout(A.a[1])+"]"

def checkPy(A,formula,info=False):
  B=range(A.cardinality)
  j=A.operations["+"]
  m=A.operations["*"]
  c=A.operations["'"]
  fm=parse(formula)
  py=pythonout(fm)
  va=sorted(formulavars(fm))
  #if info: print(py,va)
  evalst = "[("+",".join(va)+")"+"".join(" for "+v+" in B" for v in va)+' if not ('+py+')]'
  if info: print(evalst)
  li = eval(evalst,{'B':B,'m':m,'j':j,'c':c})
  if info: return li
  return li==[]

po=["x<=x","x<=y & y<=x -> x=y","x<=y & y<=z -> x<=z"]
msl=["(x^y)^z=x^(y^z)","x^y=y^x","x^x=x","x^y=x<->x<=y"]
jsl=["(x v y)v z=x v(y v z)","x v y=y v x","x v x=x","x v y=y<->x<=y"]
lat=msl+jsl+["x v(x^y)=x","x^(x v y)=x"]
dlat=lat+["x^(y v z)=(x^y)v(x^z)"]
to=lat+["x^y=x | x^y=y"] #["x<=y | y<=x"]
ba=dlat+["x'v x=t","x'^x=b"]
uo=[]
axioms=[po,jsl,msl,lat,dlat,to,ba,uo]

def tz_posets(st): #return list of tikz diagrams
    return re.findall(r"(\\begin{tikzpicture}\[xscale=1.*?\\end{tikzpicture}\n)",latex_st,flags=re.DOTALL)

def allnodes(st): #return list of node names in st
    li=re.findall(r"\\node\((.*?)\)",st,flags=re.DOTALL)
    print("Number of nodes:", len(li))
    return li

def lowercovers(nd,st): #return list of lowercovers of node name nd in st
    edges=re.search(r"\\draw\("+nd+"\)(.*?);",st,flags=re.DOTALL)
    return re.findall(r"edge.*?\((.*?)\)",edges.group(1),flags=re.DOTALL) if edges!=None else []

def lc2uc(lc):
    uc={x:[] for x in lc}
    for x in lc:
        for y in lc[x]:
            if y in uc: uc[y].append(x)
    return uc

def uc2p9(uc):
    return [(f"{i}<={j}" if j in uc[i] else f"-({i}<={j})") for i in uc for j in uc]

def opstr(m):  # convert 2-dim list to a compact string for display
    nr = len(m)
    if nr == 0:
        return "[]"
    nc = len(m[0])
    s = [[str(y).replace(' ', '') for y in x] for x in m]
    width = [max([len(s[x][y]) for x in range(nr)]) for y in range(nc)]
    s = [[" "*(width[y]-len(s[x][y]))+s[x][y] for y in range(nc)]
         for x in range(nr)]
    rows = ["["+",".join(x)+"]" for x in s]
    s = "[\n"+",\n".join(rows)+"]"
    return s


def oprelstr(oprel):  # convert a list of operations or relations to a string
    st = ''
    for x in oprel:
        if type(oprel[x]) == list and type(oprel[x][0]) == list:
            st += '\n"'+x+'":' + opstr(oprel[x]) + ', '
        else:
            st += '"'+x+'":' + str(oprel[x]) + ', '
    return st[:-2]


def op_var_pos_diag(op, s, c):
    if type(op[s]) == list:
        base = range(len(op[s]))
        if type(op[s][0]) == list:
            return [c+str(x)+" "+s+" "+c+str(y)+" = "+c+str(op[s][x][y])
                    for x in base for y in base]
        elif s == "'":
            return [c+str(x)+s+" = "+c+str(op[s][x]) for x in base]
        else:
            return [s+"("+c+str(x)+") = "+c+str(op[s][x]) for x in base]
    else:
        return [s+" = "+c+str(op[s])]


def rel_var_pos_diag(rel, s, c):
    if type(rel[s]) == list:
        base = range(len(rel[s]))
        if type(rel[s][0]) == list:
            if type(rel[s][0][0]) == list:  # if prefix ternary relation
                return [s+"("+c+str(x)+","+c+str(y)+","+c+str(z)+")"
                        for x in base for y in base for z in base if rel[s][x][y][z]]
            else:  # if infix binary relation
                return [c+str(x)+" "+s+" "+c+str(y)
                        for x in base for y in base if rel[s][x][y]]
        else:
            return [s+"("+c+str(x)+")" for x in base if rel[s][x]]
    else:
        return "not a relation"


def op_var_diag(op, s, c, n=0):
    if type(op[s]) == list:
        base = range(len(op[s]))
        if type(op[s][0]) == list:
            return [c+str(x+n)+" "+s+" "+c+str(y+n)+" = "+c+str(op[s][x][y]+n)
                    for x in base for y in base]
        elif s == "'":
            return [c+str(x+n)+s+" = "+c+str(op[s][x]+n) for x in base]
        else:
            return [s+"("+c+str(x+n)+") = "+c+str(op[s][x]+n) for x in base]
    else:
        return [s+" = "+c+str(op[s]+n)]


def rel_var_diag(rel, s, c, n=0):
    if type(rel[s]) == list:
        base = range(len(rel[s]))
        if type(rel[s][0]) == list:
            if type(rel[s][0][0]) == list:  # prefix ternary relation
                return [("" if rel[s][x][y][z] else "-")+s+"("+c+str(x+n) +
                        ","+c+str(y+n)+","+c+str(z+n)+")"
                        for x in base for y in base for z in base]
            elif s >= "A" and s <= "Z":  # prefix binary relation
                return [("" if rel[s][x][y] else "-")+s+"("+c+str(x+n) +
                        ","+c+str(y+n)+")" for x in base for y in base]
            else:  # infix binary relation
                return [("(" if rel[s][x][y] else "-(")+c+str(x+n)+" " +
                        s+" "+c+str(y+n)+")" for x in base for y in base]
        else:
            return [("" if rel[s][x] else "-")+s+"("+c+str(x+n)+")"
                    for x in base]
    else:
        return "not a relation"


def op_hom(A, B):  # return string of homomorphism equations
    st = ''
    for s in B.operations:
        if type(B.operations[s]) == list:
            if type(B.operations[s][0]) == list:
                st += " & h(x "+s+" y) = h(x) "+s+" h(y)"
            elif s == "'":
                st += " & h(x') = h(x)'"
            else:
                st += " & h("+s+"(x)) = "+s+"(h(x))"
        else:
            st += " & h("+str(B.operations[s] +
                              A.cardinality)+") = "+str(A.operations[s])
    return st


def aritystr(t): return ("(_,_)" if type(
    t[0]) == list else "(_)") if type(t) == list else ""


def op2li(t): return ([x for y in t for x in y] if type(
    t[0]) == list else t) if type(t) == list else [t]


class Model():
    def __init__(self, cardinality, index=None, operations={}, relations={},
                 **kwargs):
        """
        Construct a finite first-order model.

        INPUT:
            cardinality -- number of elements of the model's base set
            index -- a natural number giving the position of the model 
                in a list of models
            operations  -- a dictionary of operations on [0..cardinality-1].
                Entries are symbol:table pairs where symbol is a string 
                that denotes the operation symbol, e.g. '+', and table is
                an n-dimensional array with entries from [0..cardinality-1].
                n >= 0 is the arity of the operation (not explicitly coded 
                but can be computed from the table).
            relations -- a dictionary of relations on [0..cardinality-1].
                Entries are symbol:table pairs where symbol is a string 
                that denotes the relation symbol, e.g. '<', and table is
                an n-dimensional array with entries from [0,1] (coding 
                False/True). Alternatively the table can be an 
                (n-2)-dimensional array with entries that are dictionaries
                with keys [0..cardinality-1] and values subsets of [0..cardinality-1],
                given as ordered lists.
                n >= 0 is the arity of the relation (not explicitly coded 
                but can be computed from the table).
            other optional arguments --
                uc  -- a dictionary with keys [0..cardinality-1] and values 
                    an ordered list of upper covers. Used for posets.
                pos -- list of [x,y] coordinates for element positions
                labels -- list of n strings that give a label for each element
                is_... -- True/False properties are stored here
        """

        self.cardinality = cardinality
        self.index = index
        self.operations = operations
        self.relations = relations
        for attr in kwargs:
            setattr(self, attr, kwargs[attr])

    def __repr__(self):
        """
        display a model
        """
        st = '\nModel(cardinality = '+str(self.cardinality) +\
             (', index = '+str(self.index) if self.index != None else '')
        if self.operations != {}:
            st += ',\noperations = {' + oprelstr(self.operations) + '}'
        if self.relations != {}:
            st += ',\nrelations = {' + oprelstr(self.relations) + '}'
        other = set(vars(self)) - \
            set(["cardinality", "index", "operations", "relations"])
        for attr in other:
            st += ',\n' + attr + ' = ' + str(getattr(self, attr))
        return st + ')'

    def positive_diagram(self, c):
        """
        Return the positive diagram of the algebra or structure
        """
        li = []
        for x in self.operations:
            li += op_var_pos_diag(self.operations, x, c)
        for x in self.relations:
            li += rel_var_pos_diag(self.relations, x, c)
        return li

    def diagram(self, c, s=0):
        """
        Return the diagram of the algebra or structure, prefix c, shift s
        """
        li = []
        for x in range(self.cardinality):
            for y in range(x+1, self.cardinality):
                li += ["-("+c+str(x+s)+"="+c+str(y+s)+")"]
        for x in self.operations:
            li += op_var_diag(self.operations, x, c, s)
        for x in self.relations:
            li += rel_var_diag(self.relations, x, c, s)
        return li

    def find_extensions(self, cls, cardinality, mace_time=60):
        """
        Find extensions of this model of given cardinality card in FOclass cls
        """
        n = self.cardinality
        ne = ['c'+str(x)+'!=c'+str(y) for x in range(n) for y in range(x+1, n)]
        return prover9(cls.axioms+ne+self.positive_diagram('c'), [],
                       mace_time, 0, cardinality)

    def inS(self, B, info=False):
        """
        check if self is a subalgebra of B, if so return sublist of B
        """
        if self.cardinality > B.cardinality:
            return False
        if info:
            print(self.diagram('a')+B.diagram(''))
        m = prover9(self.diagram('a')+B.diagram(''), [],
                    6000, 0, B.cardinality, [], True)
        if len(m) == 0:
            return False
        return [m[0].operations['a'+str(i)] for i in range(self.cardinality)]

    def inH(self, B, info=False):
        """
        check if self is a homomorphic image of B, if so return homomorphism
        """
        if self.cardinality > B.cardinality:
            return False
        formulas = self.diagram('')+B.diagram('', self.cardinality) +\
            ['A('+str(i)+')' for i in range(self.cardinality)] +\
            ['-B('+str(i)+')' for i in range(self.cardinality)] +\
            ['B('+str(i)+')' for i in range(self.cardinality, self.cardinality+B.cardinality)] +\
            ['-A('+str(i)+')' for i in range(self.cardinality, self.cardinality+B.cardinality)] +\
            ['B(x) & B(y) -> A(h(x)) & A(h(y))'+op_hom(self, B),
             'A(y) -> exists x (B(x) & h(x) = y)']
        if info:
            print(formulas)
        m = prover9(formulas, [], 6000, 0,
                    self.cardinality+B.cardinality, [], True)
        if len(m) == 0:
            return False
        return m[0].operations['h'][self.cardinality:]

    def product(self, B, info=False):
        base = [[x,y] for x in range(self.cardinality) for y in range (B.cardinality)]
        if info: print(base)
        op = {}
        for f in B.operations:
            fA = self.operations[f]
            fB = B.operations[f]
            if type(fB)==list:
                if type(fB[0])==list:
                    op[f] = [[base.index([fA[p[0]][q[0]],fB[p[1]][q[1]]])
                               for p in base] for q in base]
                else:
                    op[f] = [base.index([fA[p[0]],fB[p[1]]]) for p in base]
            else:
                op[f] = base.index([fA,fB])
        rel = {}
        for r in B.relations:
            rA = self.relations[r]
            rB = B.relations[r]
            if type(rB[0])==list:
                rel[r] = [[1 if rA[p[0]][q[0]]==1 and rB[p[1]][q[1]]==1 else 0
                             for p in base] for q in base]
            else:
                rel[r] =[1 if rA[p[0]]==1 and rB[p[1]]==1 else 0 for p in base]
        return Model(len(base),None,op,rel)

    def uacalc_format(self, name):
        """
        display a model in UAcalc format (uacalc.org)
        """
        st = '<?xml version="1.0"?>\n<algebra>\n  <basicAlgebra>\n    <algName>'+\
             name+(str(self.index) if self.index!=None else '')+\
             '</algName>\n    <cardinality>'+str(self.cardinality)+\
             '</cardinality>\n    <operations>\n'
        for x in self.operations:
            st += '      <op>\n        <opSymbol>\n          <opName>'+\
                  x+'</opName>\n'
            oplst = type(self.operations[x]) == list
            if oplst and type(self.operations[x][0]) == list:
                st += '          <arity>2</arity>\n        </opSymbol>\n        <opTable>\n          <intArray>\n' + xmlopstr(self.operations[x])
            else:
                st += '          <arity>'+('1' if oplst else '0')+'</arity>\n        </opSymbol>\n        <opTable>\n          <intArray>\n            <row>' + (str(self.operations[x])[1:-1] if oplst else str(self.operations[x]))+'</row>\n'
            st += '          </intArray>\n        </opTable>\n      </op>\n'
        return st+'    </operations>\n  </basicAlgebra>\n</algebra>\n'

    @staticmethod
    def mace4format(A):
        if A.is_lattice():
            A.get_join()
        st = "interpretation("+str(A.cardinality) + \
            ", [number = "+str(A.index)+", seconds = 0], [\n"
        st += ',\n'.join([" function("+s+aritystr(A.operations[s])+", " +
                          str(op2li(A.operations[s])).replace(" ", "")+")" for s in A.operations])
        if len(A.operations) > 0 and len(A.relations) > 0:
            st += ',\n'
        st += ',\n'.join([" relation("+s+aritystr(A.relations[s])+", " +
                          str(op2li(A.relations[s])).replace(" ", "")+")" for s in A.relations])
        return st+"])."

import networkx as nx
from graphviz import Graph
from IPython.display import display_html
def hasse_diagram(op,rel,dual,unary=[]):
    A = range(len(op))
    G = nx.DiGraph()
    if rel:
        G.add_edges_from([(x,y) for x in A for y in A if (op[y][x] if dual else op[x][y]) and x!=y])
    else: 
        G.add_edges_from([(x,y) for x in A for y in A if op[x][y]==(y if dual else x) and x!=y])
    try:
        G = nx.algorithms.dag.transitive_reduction(G)
    except:
        pass
    P = Graph()
    P.attr('node', shape='circle', width='.15', height='.15', fixedsize='true', fontsize='10')
    for x in A: P.node(str(x), color='red' if unary[x] else 'black')
    P.edges([(str(x[0]),str(x[1])) for x in G.edges])
    return P

def show(li,symbols="<= +", unaryRel=""):
    if type(li)!=list: li = [li]
    # use graphviz to display a mace4 structure as a diagram
    # symbols is a list of binary symbols that define a poset or graph
    # unaryRel is a unary relation symbol that is displayed by red nodes
    i = 0
    sy = symbols.split(" ")
    #print(sy)
    st = ""
    for x in li:
        st+=str(i)
        i+=1
        uR = x.relations[unaryRel] if unaryRel!="" else [0]*x.cardinality
        for s in sy:
            t = s[:-1] if s[-1]=='d' else s
            if t in x.operations.keys():
                st+=hasse_diagram(x.operations[t],False,s[-1]=='d',uR)._repr_svg_()+"&nbsp; &nbsp; &nbsp; "
            elif t in x.relations.keys():
                st+=hasse_diagram(x.relations[t], True, s[-1]=='d',uR)._repr_svg_()+"&nbsp; &nbsp; &nbsp; "
        st+=" &nbsp; "
    display_html(st,raw=True)

def is_separated(G):
    for i in range(len(G)):
        for j in range(i+1,len(G)):
            if set(G[i])==set(G[j]): return False
    return True

def polar(G,X):
    if len(X)==0: return set(range(len(G)))
    return set.intersection(*[set(G[x]) for x in X])

def cl(G,x):
    if len(G[x])==0: return set(range(len(G)))
    return set.intersection(*[set(G[y]) for y in G[x]])

def is_reduced(G):
    # check cl(cl(x)-{x}) is a proper subset of cl(x)
    for x in range(len(G)):
        c = cl(G,x)
        if polar(G,polar(G,c-set([x])))==c: return False
    return True

def gclosed_sets(G):
    # compute the closed sets of a reduced graph (does not work for digraphs)
    # calculate polars of singletons and close under intersections
    clist = [frozenset(range(len(G)))]+[frozenset(G[x]) for x in range(len(G))]
    cset = set(clist)
    i = 1
    while i < len(clist):
        j = 0
        while j < i:
            c = clist[i].intersection(clist[j])
            if not(c in cset):
                cset = cset.union([c])
                clist.append(c)
            j += 1
        i += 1
    return sorted(clist, key=lambda x: len(x))#[list(x) for x in clist]

def GaloisLattice(G):
    cs = gclosed_sets(G)
    leq = [[cs[i] <= cs[j] for i in range(len(cs))] for j in range(len(cs))]
    return Model(len(cs),relations={"<=":leq})

def DeMorganLattice(G):
    cs = gclosed_sets(G)
    leq = [[cs[i] <= cs[j] for j in range(len(cs))] for i in range(len(cs))]
    dmMap = [cs.index(polar(G,cs[i])) for i in range(len(cs))]

from graphviz import Graph
from IPython.display import display_html
def diagram(g):
  P = Graph(engine='neato')
  P.attr('node', shape='circle', width='.15', height='.15', fixedsize='true', fontsize='10')
  P.edges([(str(i),str(j)) for i in range(len(g)) for j in g[i] if i>j])
  return P

def showg(li): #display an undirected graph
  i = 0
  st = ""
  for x in li:
    i+=1
    st+=str(i)
    st+=diagram(x)._repr_svg_()+"&nbsp; &nbsp; &nbsp; &nbsp; "
  display_html(st,raw=True)
