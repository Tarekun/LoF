//! JSON emission: serializing an AST (or a token stream, for
//! `--tokens` debugging) to `serde_json`, with optional pretty-printing
//! and span-stripping.

use serde::Serialize;
use serde_json::Value;

use crate::error::LeanError;

/// Recursively removes every `"span"` key from a JSON value. Simpler
/// and far less invasive than plumbing a "should I serialize my span"
/// flag through every AST type's `Serialize` impl.
pub fn strip_spans(value: &mut Value) {
    match value {
        Value::Object(map) => {
            map.remove("span");
            for v in map.values_mut() {
                strip_spans(v);
            }
        }
        Value::Array(items) => {
            for v in items.iter_mut() {
                strip_spans(v);
            }
        }
        _ => {}
    }
}

/// Serializes `value` to a JSON string, honouring `pretty` and
/// `no_spans`.
pub fn to_json_string<T: Serialize>(
    value: &T,
    pretty: bool,
    no_spans: bool,
) -> Result<String, LeanError> {
    let mut json = serde_json::to_value(value)?;
    if no_spans {
        strip_spans(&mut json);
    }
    if pretty {
        Ok(serde_json::to_string_pretty(&json)?)
    } else {
        Ok(serde_json::to_string(&json)?)
    }
}

#[cfg(test)]
mod unit_tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn strip_spans_removes_nested_span_keys() {
        let mut v = json!({
            "kind": "app",
            "span": {"start": 0, "end": 1},
            "args": [
                {"kind": "var", "span": {"start": 2, "end": 3}}
            ]
        });
        strip_spans(&mut v);
        assert_eq!(
            v,
            json!({
                "kind": "app",
                "args": [{"kind": "var"}]
            })
        );
    }

    #[test]
    fn to_json_string_respects_pretty_flag() {
        let v = json!({"a": 1});
        let compact = to_json_string(&v, false, false).unwrap();
        let pretty = to_json_string(&v, true, false).unwrap();
        assert!(!compact.contains('\n'));
        assert!(pretty.contains('\n'));
    }
}
