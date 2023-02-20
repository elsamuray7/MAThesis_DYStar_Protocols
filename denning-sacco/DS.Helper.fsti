module DS.Helper


open CryptoLib


val split_is_split_len_prefixed: b:bytes ->
  Lemma (split b == split_len_prefixed 4 b)
