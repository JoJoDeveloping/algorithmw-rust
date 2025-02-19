mod w;
use w::*;

#[cfg(test)]
mod test {
    use std::collections::HashMap;

    use crate::{
        w::{Error, Exp},
        *,
    };

    fn assert_types_at(e: Exp, et: &str) {
        let r = run2(e);
        if let Ok(t) = r {
            let t = rename_type_consistently(t, &mut HashMap::new());
            assert_eq!(format!("{t}"), et)
        } else {
            assert!(false)
        }
    }

    fn assert_unif_failure(e: Exp) {
        assert!(matches!(run2(e), Err(Error::UnificationFailure(_))))
    }

    fn assert_occurs_failure(e: Exp) {
        assert!(matches!(run2(e), Err(Error::OccursCheck(_))))
    }

    fn rename_type_consistently(t: Type, m: &mut HashMap<TypeVar, TypeVar>) -> Type {
        match t {
            Type::Var(tv) => match m.get(&tv) {
                Some(tvnew) => Type::Var(*tvnew),
                None => {
                    let ntv = TypeVar(m.len());
                    m.insert(tv, ntv);
                    Type::Var(ntv)
                }
            },
            Type::Int => Type::Int,
            Type::Bool => Type::Bool,
            Type::Str => Type::Str,
            Type::Fun(t1, t2) => Type::Fun(
                Box::new(rename_type_consistently(*t1, m)),
                Box::new(rename_type_consistently(*t2, m)),
            ),
        }
    }

    #[test]
    fn test_lit() {
        assert_types_at(lit(5), "Int");
    }
    #[test]
    fn test_str() {
        assert_types_at(lit("hello"), "Str");
    }
    #[test]
    fn test_true() {
        assert_types_at(lit(true), "Bool");
    }
    #[test]
    fn test_add() {
        assert_types_at(app(app(var("+"), lit(1)), lit(2)), "Int");
    }
    #[test]
    fn test_fail_add_bool() {
        assert_unif_failure(app(app(var("+"), lit(true)), lit(false)));
    }
    #[test]
    fn test_neg() {
        assert_types_at(app(var("-"), lit(5)), "Int");
    }
    #[test]
    fn test_fail_neg_bool() {
        assert_unif_failure(app(var("-"), lit("test")));
    }
    #[test]
    fn test_id_1() {
        assert_types_at(bind("id", abs("x", var("x")), var("id")), "('t0 → 't0)");
    }
    #[test]
    fn test_app() {
        assert_types_at(bind("five", abs("x", lit(5)), var("five")), "('t0 → Int)");
    }
    #[test]
    fn test_id_id() {
        assert_types_at(
            bind("id", abs("x", var("x")), app(var("id"), var("id"))),
            "('t0 → 't0)",
        );
    }
    #[test]
    fn test_let_simple() {
        assert_types_at(
            bind(
                "id",
                abs("x", bind("y", var("x"), var("y"))),
                app(var("id"), var("id")),
            ),
            "('t0 → 't0)",
        );
    }
    #[test]
    fn test_let_generic() {
        assert_types_at(
            bind(
                "id",
                abs("x", bind("y", var("x"), var("y"))),
                app(app(var("id"), var("id")), lit(2)),
            ),
            "Int",
        );
    }
    #[test]
    fn test_id_inst() {
        assert_occurs_failure(bind("id", abs("x", app(var("x"), var("x"))), var("id")));
    }
    #[test]
    fn test_let_nested() {
        assert_types_at(
            abs(
                "m",
                bind("y", var("m"), bind("x", app(var("y"), lit(true)), var("x"))),
            ),
            "((Bool → 't0) → 't0)",
        );
    }
    #[test]
    fn test_int_not_func() {
        assert_unif_failure(app(lit(2), lit(2)));
    }
    #[test]
    fn test_large_let() {
        assert_types_at(
            abs(
                "a",
                bind(
                    "x",
                    abs(
                        "b",
                        bind("y", abs("c", app(var("a"), lit(1))), app(var("y"), lit(2))),
                    ),
                    app(var("x"), lit(3)),
                ),
            ),
            "((Int → 't0) → 't0)",
        );
    }
    #[test]
    fn test_large_let_used() {
        assert_types_at(
            app(
                abs(
                    "a",
                    bind(
                        "x",
                        abs(
                            "b",
                            bind("y", abs("c", app(var("a"), lit(1))), app(var("y"), lit(2))),
                        ),
                        app(var("x"), lit(3)),
                    ),
                ),
                abs("x", var("x")),
            ),
            "Int",
        );
    }
    #[test]
    fn test_fixpoint_1() {
        assert_occurs_failure(abs(
            "f",
            app(
                abs("x", app(var("f"), app(var("x"), var("x")))),
                abs("x", app(var("f"), app(var("x"), var("x")))),
            ),
        ));
    }
    #[test]
    fn test_fixpoint_2() {
        assert_occurs_failure(app(
            abs(
                "f",
                app(
                    abs("x", app(var("f"), app(var("x"), var("x")))),
                    abs("x", app(var("f"), app(var("x"), var("x")))),
                ),
            ),
            abs("x", var("x")),
        ));
    }
    #[test]
    fn test_church_true() {
        assert_types_at(abs("x", abs("y", var("x"))), "('t0 → ('t1 → 't0))");
    }
    #[test]
    fn test_church_false() {
        assert_types_at(abs("x", abs("y", var("y"))), "('t0 → ('t1 → 't1))");
    }
    #[test]
    fn test_eat2() {
        assert_types_at(
            bind(
                "id",
                abs("x", var("x")),
                bind(
                    "eat2",
                    abs("x", abs("y", lit("foo"))),
                    app(
                        app(var("eat2"), app(var("id"), lit(1))),
                        app(var("id"), lit(true)),
                    ),
                ),
            ),
            "Str",
        );
    }
    #[test]
    fn test_redefine_add() {
        assert_types_at(
            bind(
                "+",
                abs("x", app(var("+"), var("x"))),
                app(app(var("+"), lit(1)), lit(2)),
            ),
            "Int",
        );
    }
    #[test]
    fn test_big_omega() {
        assert_occurs_failure(app(
            abs("x", app(var("x"), var("x"))),
            abs("x", app(var("x"), var("x"))),
        ));
    }
    #[test]
    fn test_omega() {
        assert_occurs_failure(abs("x", app(var("x"), var("x"))));
    }
    #[test]
    fn test_omega_2() {
        assert_occurs_failure(app(abs("x", app(var("x"), var("x"))), abs("x", var("x"))));
    }
    #[test]
    fn test_large_term() {
        assert_types_at(
            bind(
                "zero",
                abs("f", abs("x", var("x"))),
                bind(
                    "succ",
                    abs(
                        "n",
                        abs(
                            "f",
                            abs("x", app(var("f"), app(app(var("n"), var("f")), var("x")))),
                        ),
                    ),
                    app(
                        var("succ"),
                        app(
                            var("succ"),
                            app(
                                var("succ"),
                                app(
                                    var("succ"),
                                    app(
                                        var("succ"),
                                        app(
                                            var("succ"),
                                            app(
                                                var("succ"),
                                                app(var("succ"), app(var("succ"), var("zero"))),
                                            ),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
            "(('t0 → 't0) → ('t0 → 't0))",
        );
    }
    #[test]
    fn test_large_type() {
        // this case produces an incredibly large type
        let mut rty = Type::Fun(
            Box::new(Type::Fun(
                Box::new(Type::Var(TypeVar(0))),
                Box::new(Type::Var(TypeVar(0))),
            )),
            Box::new(Type::Var(TypeVar(1))),
        );
        for _ in 0..9 {
            rty = Type::Fun(Box::new(rty.clone()), Box::new(rty));
        }
        assert_types_at(
            bind(
                "zero",
                abs("f", abs("x", var("x"))),
                bind(
                    "succ",
                    abs(
                        "n",
                        abs(
                            "f",
                            abs("x", app(var("f"), app(var("n"), app(var("f"), var("x"))))),
                        ),
                    ),
                    app(
                        var("succ"),
                        app(
                            var("succ"),
                            app(
                                var("succ"),
                                app(
                                    var("succ"),
                                    app(
                                        var("succ"),
                                        app(
                                            var("succ"),
                                            app(
                                                var("succ"),
                                                app(var("succ"), app(var("succ"), var("zero"))),
                                            ),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
            &format!("{rty}"),
        );
    }
}

fn run2(exp: Exp) -> Result<Type> {
    let mut env: TypeEnv = TypeEnv::new();
    let mut tvg = TypeVarGen::new();

    // insert some predefined functions:
    // + :: int -> int -> int -- binary addition
    env.insert(
        "+".into(),
        Polytype {
            vars: Vec::new(),
            ty: tfun(Type::Int, tfun(Type::Int, Type::Int)),
        },
    );
    // - :: int -> int -- unary negation
    env.insert(
        "-".into(),
        Polytype {
            vars: Vec::new(),
            ty: tfun(Type::Int, Type::Int),
        },
    );
    env.type_inference(&exp, &mut tvg)
}

// Run a test case
fn test(exp: Exp) {
    println!("INPUT: {}", exp);
    match run2(exp) {
        Ok(ty) => println!("OUTPUT: {}", ty),
        Err(e) => println!("FAIL: {}", e),
    }
    println!("");
}

// Helper functions to define programs easily
fn tfun(i: Type, o: Type) -> Type {
    Type::Fun(Box::new(i), Box::new(o))
}
fn bind(name: &str, e1: Exp, e2: Exp) -> Exp {
    Exp::Let(name.into(), Box::new(e1), Box::new(e2))
}
fn abs(var: &str, e: Exp) -> Exp {
    Exp::Abs(var.into(), Box::new(e))
}
fn app(e1: Exp, e2: Exp) -> Exp {
    Exp::App(Box::new(e1), Box::new(e2))
}
fn lit<T>(i: T) -> Exp
where
    T: Into<Lit>,
{
    Exp::Lit(i.into())
}
fn var(name: &str) -> Exp {
    Exp::Var(name.into())
}

fn main() {
    test(lit(5));
    test(lit("hello"));
    test(lit(true));
    test(app(app(var("+"), lit(1)), lit(2)));
    test(app(app(var("+"), lit(true)), lit(false)));
    test(app(var("-"), lit(5)));
    test(app(var("-"), lit("test")));
    test(bind("id", abs("x", var("x")), var("id")));
    test(bind("five", abs("x", lit(5)), var("five")));
    test(bind("id", abs("x", var("x")), app(var("id"), var("id"))));
    test(bind(
        "id",
        abs("x", bind("y", var("x"), var("y"))),
        app(var("id"), var("id")),
    ));
    test(bind(
        "id",
        abs("x", bind("y", var("x"), var("y"))),
        app(app(var("id"), var("id")), lit(2)),
    ));
    test(bind("id", abs("x", app(var("x"), var("x"))), var("id")));
    test(abs(
        "m",
        bind("y", var("m"), bind("x", app(var("y"), lit(true)), var("x"))),
    ));
    test(app(lit(2), lit(2)));
    test(abs(
        "a",
        bind(
            "x",
            abs(
                "b",
                bind("y", abs("c", app(var("a"), lit(1))), app(var("y"), lit(2))),
            ),
            app(var("x"), lit(3)),
        ),
    ));
    test(app(
        abs(
            "a",
            bind(
                "x",
                abs(
                    "b",
                    bind("y", abs("c", app(var("a"), lit(1))), app(var("y"), lit(2))),
                ),
                app(var("x"), lit(3)),
            ),
        ),
        abs("x", var("x")),
    ));

    test(abs(
        "f",
        app(
            abs("x", app(var("f"), app(var("x"), var("x")))),
            abs("x", app(var("f"), app(var("x"), var("x")))),
        ),
    ));

    test(app(
        abs(
            "f",
            app(
                abs("x", app(var("f"), app(var("x"), var("x")))),
                abs("x", app(var("f"), app(var("x"), var("x")))),
            ),
        ),
        abs("x", var("x")),
    ));
    test(abs("x", abs("y", var("x")))); // true
    test(abs("x", abs("y", var("y")))); // false
    test(bind(
        "id",
        abs("x", var("x")),
        bind(
            "eat2",
            abs("x", abs("y", lit("foo"))),
            app(
                app(var("eat2"), app(var("id"), lit(1))),
                app(var("id"), lit(true)),
            ),
        ),
    ));
    test(bind(
        "+",
        abs("x", app(var("+"), var("x"))),
        app(app(var("+"), lit(1)), lit(2)),
    ));
    test(app(
        abs("x", app(var("x"), var("x"))),
        abs("x", app(var("x"), var("x"))),
    ));
    test(abs("x", app(var("x"), var("x"))));
    test(app(abs("x", app(var("x"), var("x"))), abs("x", var("x"))));

    // the output on this case is correct but nondeterministic because of the random iteration
    // order of Rust's HashMaps and HashSets
    test(bind(
        "zero",
        abs("f", abs("x", var("x"))),
        bind(
            "succ",
            abs(
                "n",
                abs(
                    "f",
                    abs("x", app(var("f"), app(app(var("n"), var("f")), var("x")))),
                ),
            ),
            app(
                var("succ"),
                app(
                    var("succ"),
                    app(
                        var("succ"),
                        app(
                            var("succ"),
                            app(
                                var("succ"),
                                app(
                                    var("succ"),
                                    app(
                                        var("succ"),
                                        app(var("succ"), app(var("succ"), var("zero"))),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    ));

    // this case produces an incredibly large type
    test(bind(
        "zero",
        abs("f", abs("x", var("x"))),
        bind(
            "succ",
            abs(
                "n",
                abs(
                    "f",
                    abs("x", app(var("f"), app(var("n"), app(var("f"), var("x"))))),
                ),
            ),
            app(
                var("succ"),
                app(
                    var("succ"),
                    app(
                        var("succ"),
                        app(
                            var("succ"),
                            app(
                                var("succ"),
                                app(
                                    var("succ"),
                                    app(
                                        var("succ"),
                                        app(var("succ"), app(var("succ"), var("zero"))),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    ));
}
