use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::Hash;
use std::ops::{Deref, DerefMut};
use std::result;

// Define our error monad
pub type Result<T> = result::Result<T, Error>;
pub enum Error {
    OccursCheck(String),
    UnificationFailure(String),
    UnboundVariable(String),
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::OccursCheck(msg) => write!(f, "occur check fails: {}", msg),
            Error::UnificationFailure(msg) => write!(f, "types do not unify: {}", msg),
            Error::UnboundVariable(msg) => write!(f, "unbound variable: {}", msg),
        }
    }
}

/// A term variable is a variable referenced in an expression
pub type TermVar = String;

/// An expression
#[derive(Debug)]
pub enum Exp {
    Var(TermVar),
    Lit(Lit),
    App(Box<Exp>, Box<Exp>),
    Abs(TermVar, Box<Exp>),
    Let(TermVar, Box<Exp>, Box<Exp>),
}

impl fmt::Display for Exp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Exp::Var(ref x) => write!(f, "{}", x),
            &Exp::Lit(ref x) => write!(f, "{}", x),
            &Exp::App(ref e1, ref e2) => write!(f, "({} {})", e1, e2),
            &Exp::Abs(ref i, ref e) => write!(f, "λ{}.{}", i, e),
            &Exp::Let(ref i, ref e1, ref e2) => write!(f, "(let {} = {} in {})", i, e1, e2),
        }
    }
}

/// A literal value of some primitive
#[derive(Debug)]
pub enum Lit {
    Int(i64),
    Bool(bool),
    Str(String),
}

// Conversion functions
impl From<i64> for Lit {
    fn from(x: i64) -> Lit {
        Lit::Int(x)
    }
}
impl From<bool> for Lit {
    fn from(x: bool) -> Lit {
        Lit::Bool(x)
    }
}
impl<'a> From<&'a str> for Lit {
    fn from(x: &str) -> Lit {
        Lit::Str(x.into())
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Lit::Int(ref x) => write!(f, "{}", x),
            &Lit::Bool(ref x) => write!(f, "{}", x),
            &Lit::Str(ref x) => write!(f, "{:?}", x),
        }
    }
}

/// A type variable represents a type that is not constrained.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypeVar(pub usize);

impl fmt::Display for TypeVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "'t{}", self.0)
    }
}

/// A source of unique type variables.
pub struct TypeVarGen {
    supply: usize,
    global_subst: HashMap<TypeVar, Type>,
}

impl TypeVarGen {
    pub fn new() -> TypeVarGen {
        TypeVarGen {
            supply: 0,
            global_subst: HashMap::new(),
        }
    }
    pub fn next(&mut self) -> TypeVar {
        let v = TypeVar(self.supply);
        self.supply += 1;
        v
    }
}

impl TypeVarGen {
    /// Attempt to bind a type variable to a type, returning an appropriate substitution.
    fn bind(&mut self, tv: TypeVar, ty: &Type) -> Result<()> {
        // Check for binding a variable to itself
        if let &Type::Var(ref u) = ty {
            if *u == tv {
                return Ok(());
            }
        }

        match self.global_subst.get(&tv) {
            None => {
                // The occurs check prevents illegal recursive types.
                if ty.ftv(self).contains(&tv) {
                    return Err(Error::OccursCheck(format!("{} vs {}", tv, ty)));
                }

                self.global_subst.insert(tv, ty.clone());
                Ok(())
            }
            Some(t) => self.unify(&t.clone(), ty),
        }
    }

    /// Most general unifier, a substitution S such that S(self) is congruent to S(other).
    fn unify(&mut self, ty: &Type, other: &Type) -> Result<()> {
        match (ty, other) {
            // For functions, we find the most general unifier for the inputs, apply the resulting
            // substitution to the outputs, find the outputs' most general unifier, and finally
            // compose the two resulting substitutions.
            (&Type::Fun(ref in1, ref out1), &Type::Fun(ref in2, ref out2)) => {
                self.unify(in1, in2)?;
                self.unify(out1, out2)?;
                Ok(())
            }

            // If one of the types is variable, we can bind the variable to the type.
            // This also handles the case where they are both variables.
            (&Type::Var(ref v), t) => self.bind(*v, t),
            (t, &Type::Var(ref v)) => self.bind(*v, t),

            // If they are both primitives, no substitution needs to be done.
            (&Type::Int, &Type::Int) | (&Type::Bool, &Type::Bool) | (&Type::Str, &Type::Str) => {
                Ok(())
            }

            // Otherwise, the types cannot be unified.
            (t1, t2) => Err(Error::UnificationFailure(format!("{} vs {}", t1, t2))),
        }
    }

    fn resolve_fully(&self, ty: &Type) -> Type {
        match ty {
            Type::Var(tv) => match self.global_subst.get(tv) {
                Some(x) => self.resolve_fully(x),
                None => Type::Var(*tv),
            },
            Type::Fun(x, y) => Type::Fun(
                Box::new(self.resolve_fully(x)),
                Box::new(self.resolve_fully(y)),
            ),
            Type::Int => Type::Int,
            Type::Bool => Type::Bool,
            Type::Str => Type::Str,
        }
    }
}

/// A trait common to all things considered types.
trait Types {
    /// Find the set of free variables in a type.
    fn ftv(&self, globals: &TypeVarGen) -> HashSet<TypeVar>;
}

impl<'a, T> Types for Vec<T>
where
    T: Types,
{
    // The free type variables of a vector of types is the union of the free type variables of each
    // of the types in the vector.
    fn ftv(&self, globals: &TypeVarGen) -> HashSet<TypeVar> {
        self.iter()
            .map(|x| x.ftv(globals))
            .fold(HashSet::new(), |set, x| set.union(&x).cloned().collect())
    }
}

/// A monotype representing a concrete type.
#[derive(Clone, Debug)]
pub enum Type {
    Var(TypeVar),
    Int,
    Bool,
    Str,
    Fun(Box<Type>, Box<Type>),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Type::Var(ref x) => write!(f, "{}", x),
            Type::Int | Type::Bool | Type::Str => write!(f, "{:?}", self),
            Type::Fun(ref t1, ref t2) => write!(f, "({} → {})", t1, t2),
        }
    }
}

impl Types for TypeVar {
    fn ftv(&self, globals: &TypeVarGen) -> HashSet<TypeVar> {
        match globals.global_subst.get(self) {
            None => [*self].iter().copied().collect(),
            Some(x) => x.ftv(globals),
        }
    }
}

impl Types for Type {
    fn ftv(&self, g: &TypeVarGen) -> HashSet<TypeVar> {
        match self {
            // For a type variable, there is one free variable: the variable itself.
            &Type::Var(ref s) => s.ftv(g),

            // Primitive types have no free variables
            &Type::Int | &Type::Bool | &Type::Str => HashSet::new(),

            // For functions, we take the union of the free type variables of the input and output.
            &Type::Fun(ref i, ref o) => i.ftv(g).union(&o.ftv(g)).cloned().collect(),
        }
    }
}

impl Type {
    fn subst(self, map: &HashMap<TypeVar, Type>) -> Type {
        match self {
            Type::Var(tv) => match map.get(&tv) {
                Some(y) => y.clone(),
                None => Type::Var(tv),
            },
            Type::Fun(x, y) => Type::Fun(Box::new(x.subst(map)), Box::new(y.subst(map))),
            Type::Int => Type::Int,
            Type::Bool => Type::Bool,
            Type::Str => Type::Str,
        }
    }
}

/// A polytype is a type in which there are a number of for-all quantifiers, i.e. some parts of the
/// type may not be concrete but instead correct for all possible types.
#[derive(Clone, Debug)]
pub struct Polytype {
    pub vars: Vec<TypeVar>,
    pub ty: Type,
}

impl Types for Polytype {
    /// The free type variables in a polytype are those that are free in the internal type and not
    /// bound by the variable mapping.
    fn ftv(&self, g: &TypeVarGen) -> HashSet<TypeVar> {
        self.ty
            .ftv(g)
            .difference(&self.vars.iter().cloned().collect())
            .cloned()
            .collect()
    }
}

impl Polytype {
    /// Instantiates a polytype into a type. Replaces all bound type variables with fresh type
    /// variables and return the resulting type.
    fn instantiate(&self, tvg: &mut TypeVarGen) -> Type {
        let ty = tvg.resolve_fully(&self.ty);
        let newvars = self.vars.iter().map(|_| Type::Var(tvg.next()));
        ty.subst(&self.vars.iter().cloned().zip(newvars).collect())
    }
}

/// A type environment is a mapping from term variables to polytypes.
#[derive(Clone, Debug)]
pub struct TypeEnv(HashMap<TermVar, Polytype>);

impl Deref for TypeEnv {
    type Target = HashMap<TermVar, Polytype>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl DerefMut for TypeEnv {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl Types for TypeEnv {
    /// The free type variables of a type environment is the union of the free type variables of
    /// each polytype in the environment.
    fn ftv(&self, g: &TypeVarGen) -> HashSet<TypeVar> {
        self.values()
            .map(|x| x.clone())
            .collect::<Vec<Polytype>>()
            .ftv(g)
    }
}

impl TypeEnv {
    /// Construct an empty type environment.
    pub fn new() -> TypeEnv {
        TypeEnv(HashMap::new())
    }

    /// Generalize creates a polytype
    fn generalize(&self, ty: &Type, g: &mut TypeVarGen) -> Polytype {
        Polytype {
            vars: ty.ftv(g).difference(&self.ftv(g)).cloned().collect(),
            ty: ty.clone(),
        }
    }

    /// The meat of the type inference algorithm.
    fn ti(&self, exp: &Exp, tvg: &mut TypeVarGen) -> Result<Type> {
        match *exp {
            // A variable is typed as an instantiation of the corresponding type in the
            // environment.
            Exp::Var(ref v) => match self.get(v) {
                Some(s) => Ok(s.instantiate(tvg)),
                None => Err(Error::UnboundVariable(format!("{}", v))),
            },

            // A literal is typed as it's primitive type.
            Exp::Lit(ref l) => Ok(match l {
                &Lit::Int(_) => Type::Int,
                &Lit::Bool(_) => Type::Bool,
                &Lit::Str(_) => Type::Str,
            }),

            // An abstraction is typed by:
            // * Removing any existing type with the same name as the argument to prevent name
            // clashes.
            // * Inserting a new type variable for the argument.
            // * Inferring the type of the expression in the new environment to define the type of
            // the expression.
            // * Applying the resulting substitution to the argument to define the type of the
            // argument.
            Exp::Abs(ref n, ref e) => {
                let tv = Type::Var(tvg.next());
                let mut env = self.clone();
                env.remove(n);
                env.insert(
                    n.clone(),
                    Polytype {
                        vars: Vec::new(),
                        ty: tv.clone(),
                    },
                );
                let t1 = (env.ti(e, tvg))?;
                Ok(Type::Fun(Box::new(tv), Box::new(t1)))
            }

            // An application is typed by:
            // * Inferring the type of the callee.
            // * Applying the resulting substitution to the argument and inferring it's type.
            // * Finding the most general unifier for the callee type and a function from the
            // argument type to a new type variable. This combines the previously known type of the
            // function and the type as it is now being used.
            // * Applying the unifier to the new type variable.
            Exp::App(ref e1, ref e2) => {
                let t1 = (self.ti(e1, tvg))?;
                let t2 = (self.ti(e2, tvg))?;
                let tv = Type::Var(tvg.next());
                (tvg.unify(&t1, &Type::Fun(Box::new(t2), Box::new(tv.clone()))))?;
                Ok(tv)
            }

            // Let (variable binding) is typed by:
            // * Removing any existing type with the same name as the binding variable to prevent
            // name clashes.
            // * Inferring the type of the binding.
            // * Applying the resulting substitution to the environment and generalizing to the
            // binding type.
            // * Inserting the generalized type to the binding variable in the new environment.
            // * Applying the substution for the binding to the environment and inferring the type
            // of the expression.
            Exp::Let(ref x, ref e1, ref e2) => {
                let mut env = self.clone();
                env.remove(x);
                let t1 = (self.ti(e1, tvg))?;
                let tp = env.generalize(&t1, tvg);
                env.insert(x.clone(), tp);
                let t2 = (env.ti(e2, tvg))?;
                Ok(t2)
            }
        }
    }

    /// Perform type inference on an expression and return the resulting type, if any.
    pub fn type_inference(&self, exp: &Exp, tvg: &mut TypeVarGen) -> Result<Type> {
        let t = (self.ti(exp, tvg))?;
        Ok(tvg.resolve_fully(&t))
    }
}
