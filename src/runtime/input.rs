//! Bounded local fixture inputs and unambiguous JSON maps.

use anyhow::{Context as _, Result, ensure};
use serde::{
    Deserialize, Deserializer, Serialize,
    de::{Error as _, MapAccess, Visitor},
};
use std::{
    collections::{BTreeMap, btree_map::Entry},
    fmt,
    fs::File,
    io::{self, Read, Write},
    marker::PhantomData,
    path::Path,
};

// A 1 MiB input budget per file. Serialized library inputs
// are counted too, so bypassing the CLI does not bypass the fixture limit.
const MAX_INPUT_BYTES: usize = 1_048_576;
const MAX_TRANSACTIONS: usize = 256;
// Allow full-block-sized local transactions, with at most ten such transactions
// (or an equivalent smaller workload) per baseline/candidate program.
const MAX_TRANSACTION_GAS: u64 = 30_000_000;
const MAX_TOTAL_GAS: u64 = 300_000_000;

struct InputSize {
    bytes: usize,
}

impl Write for InputSize {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        if bytes.len() > MAX_INPUT_BYTES - self.bytes {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "runtime JSON exceeds the 1 MiB input limit",
            ));
        }
        self.bytes += bytes.len();
        Ok(bytes.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// Validate the complete batch before proving rewrites or executing either side.
/// Existing callers separately reject empty batches and empty sequences.
pub(super) fn validate<T: Serialize>(
    inputs: &T,
    gas_limits: impl IntoIterator<Item = u64>,
) -> Result<()> {
    let mut total_gas = 0_u64;
    for (index, gas_limit) in gas_limits.into_iter().enumerate() {
        ensure!(
            index < MAX_TRANSACTIONS,
            "runtime input exceeds {MAX_TRANSACTIONS} transactions"
        );
        ensure!(
            gas_limit <= MAX_TRANSACTION_GAS,
            "transaction {index} gas limit exceeds {MAX_TRANSACTION_GAS}"
        );
        total_gas = total_gas
            .checked_add(gas_limit)
            .context("runtime transaction gas budget overflow")?;
        ensure!(
            total_gas <= MAX_TOTAL_GAS,
            "runtime total transaction gas exceeds {MAX_TOTAL_GAS} per program"
        );
    }
    serde_json::to_writer(&mut InputSize { bytes: 0 }, inputs)
        .context("invalid runtime JSON input")?;
    Ok(())
}

/// Read at most 1 MiB of UTF-8 input, including surrounding whitespace.
/// Parsing remains with the caller so existing schemas and diagnostics persist.
pub fn read_json(path: &Path) -> Result<String> {
    let mut bytes = Vec::new();
    File::open(path)
        .with_context(|| format!("cannot open {}", path.display()))?
        .take((MAX_INPUT_BYTES + 1) as u64)
        .read_to_end(&mut bytes)
        .with_context(|| format!("cannot read {}", path.display()))?;
    ensure!(
        bytes.len() <= MAX_INPUT_BYTES,
        "{} exceeds the 1 MiB runtime input limit",
        path.display()
    );
    String::from_utf8(bytes).with_context(|| format!("{} is not UTF-8", path.display()))
}

/// Read deployed hexadecimal bytecode with the same bounded file reader.
pub fn read_bytecode(path: &Path) -> Result<Vec<u8>> {
    let code = super::from_hex(&read_json(path)?)?;
    ensure!(
        code.len() <= super::MAX_RUNTIME_BYTES,
        "runtime exceeds EIP-170 size limit"
    );
    Ok(code)
}

// Reject repeated JSON keys before collection can silently overwrite a value.
// Numeric/address aliases are checked by callers after canonical parsing.
pub(super) fn unique_map<'de, D, T>(
    deserializer: D,
) -> std::result::Result<BTreeMap<String, T>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    struct UniqueMap<T>(PhantomData<T>);
    impl<'de, T: Deserialize<'de>> Visitor<'de> for UniqueMap<T> {
        type Value = BTreeMap<String, T>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("an object with unique keys")
        }

        fn visit_map<M: MapAccess<'de>>(
            self,
            mut map: M,
        ) -> std::result::Result<Self::Value, M::Error> {
            let mut entries = BTreeMap::new();
            while let Some(key) = map.next_key::<String>()? {
                match entries.entry(key) {
                    Entry::Vacant(entry) => {
                        entry.insert(map.next_value()?);
                    }
                    Entry::Occupied(entry) => {
                        return Err(M::Error::custom(format!(
                            "duplicate map key: {}",
                            entry.key()
                        )));
                    }
                }
            }
            Ok(entries)
        }
    }
    deserializer.deserialize_map(UniqueMap(PhantomData))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::tempdir;

    #[test]
    fn gas_workloads_accept_boundaries_and_reject_excess_without_overflow() {
        validate(&(), std::iter::repeat_n(MAX_TRANSACTION_GAS, 10)).unwrap();
        validate(&(), std::iter::repeat_n(1, MAX_TRANSACTIONS)).unwrap();
        for limits in [
            vec![MAX_TRANSACTION_GAS + 1],
            vec![u64::MAX, u64::MAX],
            std::iter::repeat_n(MAX_TRANSACTION_GAS, 11).collect(),
            std::iter::repeat_n(MAX_TRANSACTION_GAS, 10)
                .chain([1])
                .collect(),
            vec![1; MAX_TRANSACTIONS + 1],
        ] {
            assert!(validate(&(), limits).is_err());
        }
        // Batch emptiness is validated by the owning execution entry point.
        validate(&(), []).unwrap();
    }

    #[test]
    fn serialized_budget_counts_utf8_and_json_escaping_in_bytes() {
        let exact = "a".repeat(MAX_INPUT_BYTES - 2); // Two JSON quote bytes.
        validate(&exact, []).unwrap();
        assert!(validate(&(exact + "a"), []).is_err());
        let exact = "é".repeat((MAX_INPUT_BYTES - 2) / 2);
        validate(&exact, []).unwrap();
        assert!(validate(&(exact + "é"), []).is_err());
        // Newlines need two serialized bytes, although each input byte is one.
        let escaped = "\n".repeat((MAX_INPUT_BYTES - 2) / 2);
        validate(&escaped, []).unwrap();
        assert!(validate(&(escaped + "\n"), []).is_err());
    }

    #[test]
    fn files_are_bounded_before_parsing_and_bytecode_has_its_own_size_limit() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("input");
        fs::write(&path, vec![b' '; MAX_INPUT_BYTES]).unwrap();
        assert_eq!(read_json(&path).unwrap().len(), MAX_INPUT_BYTES);
        fs::write(&path, vec![b' '; MAX_INPUT_BYTES + 1]).unwrap();
        assert!(read_json(&path).unwrap_err().to_string().contains("1 MiB"));
        fs::write(&path, [0xff]).unwrap();
        assert!(read_json(&path).unwrap_err().to_string().contains("UTF-8"));
        fs::write(&path, " \n0x6000\n").unwrap();
        assert_eq!(read_bytecode(&path).unwrap(), [0x60, 0]);
        fs::write(&path, "00".repeat(super::super::MAX_RUNTIME_BYTES)).unwrap();
        assert_eq!(
            read_bytecode(&path).unwrap().len(),
            super::super::MAX_RUNTIME_BYTES
        );
        fs::write(&path, "00".repeat(super::super::MAX_RUNTIME_BYTES + 1)).unwrap();
        assert!(
            read_bytecode(&path)
                .unwrap_err()
                .to_string()
                .contains("EIP-170")
        );
    }

    #[test]
    fn map_keys_cannot_silently_replace_values_and_omission_still_defaults() {
        #[derive(Debug, Deserialize)]
        struct Fixture {
            #[serde(default, deserialize_with = "unique_map")]
            storage: BTreeMap<String, String>,
        }
        assert!(
            serde_json::from_str::<Fixture>("{}")
                .unwrap()
                .storage
                .is_empty()
        );
        let fixture = serde_json::from_str::<Fixture>(r#"{"storage":{"0":"7","1":"9"}}"#).unwrap();
        assert_eq!(fixture.storage["0"], "7");
        assert_eq!(fixture.storage["1"], "9");
        for json in [
            r#"{"storage":{"0":"7","0":"0"}}"#,
            r#"{"storage":{"0":"7","\u0030":"0"}}"#,
        ] {
            assert!(
                serde_json::from_str::<Fixture>(json)
                    .unwrap_err()
                    .to_string()
                    .contains("duplicate map key: 0")
            );
        }
    }
}
