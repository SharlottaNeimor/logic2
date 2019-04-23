from formula import Formula

class Loger:
    def __init__(self,path:str):
        self.path = path
        with open(self.path,'w') as f: pass
    def write(self,F:Formula,text:str):
        with open(self.path,'a') as f:
            f.write(F()+'   '+text)