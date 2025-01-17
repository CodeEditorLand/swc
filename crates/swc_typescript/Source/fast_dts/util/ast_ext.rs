use std::borrow::Cow;

use swc_atoms::Atom;
use swc_ecma_ast::{
    BindingIdent, Expr, Lit, MemberExpr, MemberProp, ObjectPatProp, Pat, PropName, TsTypeAnn,
};

pub trait PatExt {
    fn get_type_ann(&self) -> &Option<Box<TsTypeAnn>>;
    fn set_type_ann(&mut self, type_anno: Option<Box<TsTypeAnn>>);
    fn bound_names<F: FnMut(&BindingIdent)>(&self, f: &mut F);
}

impl PatExt for Pat {
    fn get_type_ann(&self) -> &Option<Box<TsTypeAnn>> {
        let pat = match self {
            Pat::Assign(assign_pat) => &assign_pat.left,
            _ => self,
        };

        match pat {
            Pat::Ident(binding_ident) => &binding_ident.type_ann,
            Pat::Array(array_pat) => &array_pat.type_ann,
            Pat::Rest(rest_pat) => &rest_pat.type_ann,
            Pat::Object(object_pat) => &object_pat.type_ann,
            Pat::Assign(_) | Pat::Invalid(_) | Pat::Expr(_) => &None,
        }
    }

    fn set_type_ann(&mut self, type_anno: Option<Box<TsTypeAnn>>) {
        let pat = match self {
            Pat::Assign(assign_pat) => &mut assign_pat.left,
            _ => self,
        };

        match pat {
            Pat::Ident(binding_ident) => binding_ident.type_ann = type_anno,
            Pat::Array(array_pat) => array_pat.type_ann = type_anno,
            Pat::Rest(rest_pat) => rest_pat.type_ann = type_anno,
            Pat::Object(object_pat) => object_pat.type_ann = type_anno,
            Pat::Assign(_) | Pat::Invalid(_) | Pat::Expr(_) => {}
        }
    }

    fn bound_names<F: FnMut(&BindingIdent)>(&self, f: &mut F) {
        match self {
            Pat::Ident(binding_ident) => f(binding_ident),
            Pat::Array(array_pat) => {
                for pat in array_pat.elems.iter().flatten() {
                    pat.bound_names(f);
                }
            }
            Pat::Rest(rest_pat) => rest_pat.arg.bound_names(f),
            Pat::Object(object_pat) => {
                for pat in &object_pat.props {
                    match pat {
                        ObjectPatProp::KeyValue(key_value_pat_prop) => {
                            key_value_pat_prop.value.bound_names(f)
                        }
                        ObjectPatProp::Assign(assign_pat_prop) => f(&assign_pat_prop.key),
                        ObjectPatProp::Rest(rest_pat) => rest_pat.arg.bound_names(f),
                    }
                }
            }
            Pat::Assign(assign_pat) => assign_pat.left.bound_names(f),
            Pat::Invalid(_) | Pat::Expr(_) => todo!(),
        }
    }
}

pub trait PropNameExit {
    fn static_name(&self) -> Option<Cow<str>>;
}

impl PropNameExit for PropName {
    fn static_name(&self) -> Option<Cow<str>> {
        match self {
            PropName::Ident(ident_name) => Some(Cow::Borrowed(ident_name.sym.as_str())),
            PropName::Str(string) => Some(Cow::Borrowed(string.value.as_str())),
            PropName::Num(number) => Some(Cow::Owned(number.value.to_string())),
            PropName::BigInt(big_int) => Some(Cow::Owned(big_int.value.to_string())),
            PropName::Computed(computed_prop_name) => match computed_prop_name.expr.as_ref() {
                Expr::Lit(lit) => match lit {
                    Lit::Str(string) => Some(Cow::Borrowed(string.value.as_str())),
                    Lit::Bool(b) => Some(Cow::Owned(b.value.to_string())),
                    Lit::Null(_) => Some(Cow::Borrowed("null")),
                    Lit::Num(number) => Some(Cow::Owned(number.value.to_string())),
                    Lit::BigInt(big_int) => Some(Cow::Owned(big_int.value.to_string())),
                    Lit::Regex(regex) => Some(Cow::Owned(regex.exp.to_string())),
                    Lit::JSXText(_) => None,
                },
                Expr::Tpl(tpl) if tpl.exprs.is_empty() => tpl
                    .quasis
                    .first()
                    .and_then(|e| e.cooked.as_ref())
                    .map(|atom| Cow::Borrowed(atom.as_str())),
                _ => None,
            },
        }
    }
}

pub trait MemberPropExt {
    fn static_name(&self) -> Option<&Atom>;
}

impl MemberPropExt for MemberProp {
    fn static_name(&self) -> Option<&Atom> {
        match self {
            MemberProp::Ident(ident_name) => Some(&ident_name.sym),
            MemberProp::Computed(computed_prop_name) => match computed_prop_name.expr.as_ref() {
                Expr::Lit(Lit::Str(s)) => Some(&s.value),
                Expr::Tpl(tpl) if tpl.quasis.len() == 1 && tpl.exprs.is_empty() => {
                    Some(&tpl.quasis[0].raw)
                }
                _ => None,
            },
            MemberProp::PrivateName(_) => None,
        }
    }
}

pub trait MemberExprExt {
    fn get_first_object(&self) -> &Expr;
}

impl MemberExprExt for MemberExpr {
    fn get_first_object(&self) -> &Expr {
        let mut object = &self.obj;
        loop {
            match object.as_ref() {
                Expr::Member(member_expr) => {
                    object = &member_expr.obj;
                    continue;
                }
                Expr::OptChain(opt_chain) => {
                    if let Some(member_expr) = opt_chain.base.as_member() {
                        object = &member_expr.obj;
                        continue;
                    }
                }
                _ => {}
            }
            break object;
        }
    }
}
