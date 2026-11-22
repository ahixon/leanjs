import re,sys
def sig(path, name, concl_marker):
    src=open(path).read()
    i=src.index("theorem "+name); j=src.index(concl_marker, i)
    body=re.sub(r"--[^\n]*","",src[i:j])
    out=[];depth=0;cur=""
    for ch in body[body.index("{"):]:
        if ch in "({⟨[":
            if depth==0 and ch in "({": cur=""
            depth+=1
        if depth>0: cur+=ch
        if ch in ")}⟩]":
            depth-=1
            if depth==0 and ch in ")}": out.append(cur)
    imps=[b for b in out if b.startswith("{")]
    hyps=[b for b in out if b.startswith("(")]
    return imps,hyps
def names_of_imp(b):
    return b[1:b.index(":")].split()
def hname(b):
    return re.match(r"\((\w+'?)",b).group(1)
