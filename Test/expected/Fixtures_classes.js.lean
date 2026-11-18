def Animal :=
  { constructor := fun name => do
    self.name.set name
    name
, speak := fun => return self.name + " makes a noise." }

def Dog :=
  { constructor := fun name => super name, speak := fun => return self.name + " barks." }

def d :=
  Dog "Rex"
[exit 0]
