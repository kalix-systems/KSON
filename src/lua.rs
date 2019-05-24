use crate::prelude::*;
use rlua::prelude::*;

macro_rules! to_lua_bail {
    ($from:expr, $to:expr, $msg:expr) => {
        return Err(LuaError::ToLuaConversionError {
            from:    $from,
            to:      $to,
            message: $msg,
        });
    };
}

impl<'lua> ToLua<'lua> for &Kson {
    fn to_lua(self, lua: LuaContext<'lua>) -> LuaResult<LuaValue<'lua>> {
        let res = match self {
            Kson::Null => LuaValue::Nil,
            Kson::Bool(b) => LuaValue::Boolean(*b),
            Kson::Kint(x) => {
                match x {
                    Inum::Int(_) => to_lua_bail!("BigInt", "int", None),
                    Inum::I64(val) => {
                        let value = val.to_lua(lua).unwrap();
                        let obj_elems = vec![
                            ("type", LuaValue::String(lua.create_string("int").unwrap())),
                            ("value", value),
                        ];
                        LuaValue::Table(lua.create_table_from(obj_elems).unwrap())
                    }
                }
            }
            Kson::Kfloat(val) => {
                let value = f64::try_from(val.clone()).unwrap().to_lua(lua).unwrap();
                let prec = match val {
                    Float::Half(_) => "half",
                    Float::Single(_) => "single",
                    Float::Double(_) => "double",
                };
                let obj_elems = vec![
                    (
                        "type",
                        LuaValue::String(lua.create_string("float").unwrap()),
                    ),
                    ("prec", LuaValue::String(lua.create_string(prec).unwrap())),
                    ("value", value),
                ];
                LuaValue::Table(lua.create_table_from(obj_elems)?)
            }
            Kson::Byt(bs) => LuaValue::String(lua.create_string(bs).unwrap()),
            Kson::Array(arr) => {
                let items: LuaResult<Vec<LuaValue<'lua>>> =
                    arr.iter().map(|elem| elem.to_lua(lua)).collect();
                let value = LuaValue::Table(lua.create_sequence_from(items?)?);
                let obj_elems = vec![
                    ("type", LuaValue::String(lua.create_string("array")?)),
                    ("value", value),
                ];
                LuaValue::Table(lua.create_table_from(obj_elems)?)
            }
            Kson::Map(map) => {
                let items: LuaResult<Vec<(LuaValue<'lua>, LuaValue<'lua>)>> = map
                    .iter()
                    .map(|(k, v)| Ok((LuaValue::String(lua.create_string(k)?), v.to_lua(lua)?)))
                    .collect();
                let value = LuaValue::Table(lua.create_table_from(items?)?);
                let obj_elems = vec![
                    ("type", LuaValue::String(lua.create_string("map")?)),
                    ("value", value),
                ];
                LuaValue::Table(lua.create_table_from(obj_elems)?)
            }
        };
        Ok(res)
    }
}

macro_rules! from_lua_bail {
    ($from:expr, $to:expr, $msg:expr) => {
        return Err(LuaError::FromLuaConversionError {
            from:    $from,
            to:      $to,
            message: $msg,
        });
    };
}

impl<'lua> FromLua<'lua> for Kson {
    fn from_lua(val: LuaValue<'lua>, ctx: LuaContext<'lua>) -> LuaResult<Kson> {
        match val {
            LuaValue::Nil => Ok(Kson::Null),
            LuaValue::Boolean(b) => Ok(Kson::Bool(b)),
            LuaValue::String(s) => Ok(Kson::Byt(Bytes::from(s.as_bytes()))),
            LuaValue::Integer(i) => Ok(Kson::from(i)),
            LuaValue::Number(n) => Ok(Kson::from(n)),
            LuaValue::Table(obj) => {
                let typ: String = obj.get("type")?;
                let value: LuaValue = obj.get("value")?;
                if typ == "float" {
                    let num = f64::from_lua(value, ctx)?;
                    let prec: String = obj.get("prec")?;
                    let kfloat = if prec == "half" {
                        Float::from(f16::from_f64(num))
                    } else if prec == "single" {
                        Float::from(num as f32)
                    } else if prec == "double" {
                        Float::from(num)
                    } else {
                        from_lua_bail!(
                            "float",
                            "float",
                            Some(format!("bad float prec value: {}", prec))
                        )
                    };
                    Ok(Kson::Kfloat(kfloat))
                } else if typ == "array" {
                    let table = LuaTable::from_lua(value, ctx)?;
                    let kvals: LuaResult<Vec<Kson>> = table.sequence_values().collect();
                    Ok(Kson::Array(kvals?))
                } else if typ == "map" {
                    let table = LuaTable::from_lua(value, ctx)?;
                    let vs: LuaResult<Vec<(Bytes, Kson)>> = table
                        .pairs()
                        .map(|pair: LuaResult<(String, Kson)>| {
                            let (key, val) = pair?;
                            let key = Bytes::from(key.as_bytes());
                            Ok((key, val))
                        })
                        .collect();
                    Ok(Kson::Map(VecMap::from(vs?)))
                } else {
                    from_lua_bail!(
                        "custom",
                        "unknown",
                        Some(format!(
                            "unexpected type in table: {}\nvalue was: {:?}\n",
                            typ, value
                        ))
                    )
                }
            }
            v => {
                from_lua_bail!(
                    "unknown",
                    "unknown",
                    Some(format!(
                        "unexpected lua type when converting to KSON, value was:\n{:?}\n",
                        v
                    ))
                )
            }
        }
    }
}
