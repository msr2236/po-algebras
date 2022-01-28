# Signature for input and output (the LaTeX symbols can be changed to agree with other conventions)

from IPython.display import display, Math
import time

FOLang = { #Constant operation symbols
"c":(0,"c"), "d":(0,"d"), "e":(0,"e"), "0":(0,"zero"), "1":(0,"one"), "\\bot":(0,"bot"), "\\top":(0,"top"),
#Logical connectives 
"\\iff":(1,"==", <-> ), "\\implies":(2,"<="," -> "), "\\text{ or }":(3," or ","|"), "\\text{ and }":(4," and ","&"), "\\neg":(5," not "),
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
    elif FOLang[s][0]<=5: infix(s,FOLang[s][1])
    elif FOLang[s][0]<=6:
        for v in Vars:
            prefix(s+" "+v,FOLang[s][1])
            for i in range(10):
                prefix(s+" "+v+"_"+str(i),FOLang[s][1])
    elif FOLang[s][0]<=12: infix(s,FOLang[s][1])
    elif FOLang[s][0]<=13: prefix(s,FOLang[s][1])
    elif FOLang[s][0]<=14: postfix(s,FOLang[s][1])

#for st in VAR|CONST: symbol(st)
#for t in PREFIX: prefix(t[0],t[1])
#for t in POSTFIX: postfix(t[0],t[1])
#for t in INFIX: infix(t[0],t[1])
#for st in VAR:
#    for t in QUANT: prefix(t[0]+" "+st,t[1])

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

def show(A, info=True): # display a (list of) formula(s)
  st = A if type(A)==str else repr(A)
  if info==True: display(Math(Macros+st))

########### end of parser #####################################

import re

def p9out(A): #output formula A in Prover9 format
  if A.a==[]: return p9sym[A.id]
  if A.id[:7] in ["\\forall","\\exists"]:
    return p9sym[A.id[:7]]+" "+A.id[8:]+"("+p9out(A.a[0])+")"
  if len(A.a)==1:
    #if symbol_table[p9sym[A.id]].lbp!=12:
      return p9sym[A.id]+"("+p9out(A.a[0])+")"
    #return "("+p9out(A.a[0])+")"+p9sym[A.id]
  return "("+p9out(A.a[0])+p9sym[A.id]+p9out(A.a[1])+")"

po=["x<=x","x<=y & y<=x -> x=y","x<=y & y<=z -> x<=z"]
msl=["(x^y)^z=x^(y^z)","x^y=y^x","x^x=x","x^y=x<->x<=y"]
jsl=["(x v y)v z=x v(y v z)","x v y=y v x","x v x=x","x v y=y<->x<=y"]
lat=msl+jsl+["x v(x^y)=x","x^(x v y)=x"]
dlat=lat+["x^(y v z)=(x^y)v(x^z)"]
to=lat+["x^y=x | x^y=y"] #["x<=y | y<=x"]
ba=dlat+["x'v x=t","x'^x=b"]
uo=[]
axioms=[po,jsl,msl,lat,dlat,to,ba,uo]

def fd(cl,info=True,new_ax=None):
    try:
        ax = [p9out(parse(e)) for e in fulldefinition(cl)]
    except:
        print("############### Error, skipping", cl)
        return []
    ax = [(x[1:-1] if x[0]=='(' and x[-1]==')' else x) for x in ax]
    ch_axioms = axioms[fam[cl]] if new_ax==None else new_ax
    if info: 
        print(ch_axioms+ax)
    return ch_axioms+ax

def finespectrum(cl,n,info=True,new_ax=None): 
  # call Prover9 on the translated full definition of cl and find the fine spectrum up to n
    if info: print(cl)
    ax = fd(cl,new_ax)
    if ax==[]: return []
    t = time.time()
    a = [[1]]+[prover9(ch_axioms+ax,[],10000,10000,k,options=opts) for k in range(2,n+1)]
    if info: print("Time: {:.2f}".format(time.time()-t), "sec")
    return [len(x) for x in a]

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

def smallmembers(cl): #return list of small algebras of the class cl
    sm=re.search(r"\\begin{smallmembers}(.*?)\\end{smallmembers}",section(cl),flags=re.DOTALL)
    if sm==None: return 'none'
    li=re.findall(r"\\begin{tikzpicture}(.*?)\\end{tikzpicture}",sm.group(1),flags=re.DOTALL)
    pl=[list(reversed(re.findall(r"\\node\((.*?);", s,flags=re.DOTALL))) for s in li]
    uc=[{int(s[:s.index(")")]):[int(y) for y in re.findall(r"edge.*?\((.*?)\)",s)] for s in x} for x in pl]
    xy=[{int(s[:s.index(")")]):(re.search(r"\((.*?),",s).group(1), re.search(r",(.*?)\)",s).group(1)) for s in x} for x in pl]
    xy=[{i:tuple((int(z) if z.find(".")==-1 else float(z)) for z in xy[n][i]) for i in xy[n]} for n in range(len(pl))]
    c=[[int(s[:s.index(")")]) for s in x if s.find("label=")!=-1] for x in pl]
    return [({'uc':uc[n], 'xy':xy[n]} if c[n]==[] else {'uc':uc[n], 'xy':xy[n], 'c':c[n][0]}) for n in range(len(pl))]

def uc2p9(uc):
    return [(f"{i}<={j}" if j in uc[i] else f"-({i}<={j})") for i in uc for j in uc]