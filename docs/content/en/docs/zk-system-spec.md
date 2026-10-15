---
title: "Longfellow ZK System spec parameters"
linkTitle: "Zk System Spec"
weight: 100
description: >-
     List of ZK System spec parameters expected by Longfellow ZK library
---

ISO 18013-5 and and OpenId4VP allow RPs to request ZKP responses and specify any ZKP system and some parameters required to make sure RP will be able to verify the proof correctly.
The list of the parameters and their values are not defined in the standard and are specific for each ZKP system. 

This document describes which parameters should be used by users of Longfellow ZK System. Those parameters are currently used by Google Wallet and Multipaz Wallet/RP.

For the Longfellow ZK, the following parameters and values should be used:
* **zkSystemId**: <any value, we recommend using circuit_hash to avoid confusion>
* **system**: 'longfellow-libzk-v1'

The following parameters must be present:
* **circuit_hash**: The hash of the used circuit.
* **num_attributes**: The number of requested attributes.
* **version**: The circuit version.
* **block_enc_hash**: The `block_enc` parameter for the ZK proof of the hash component.
* **block_enc_sig**: The `block_enc` parameter for the ZK proof of the signature component.

**The parameters change relatively often. We are releasing new circuits regularly, so it's strongly recommended not to build ZKSpecs manually nor hardcode them, but instead to use [`kZkSpecs`](https://github.com/longfellow-zk/longfellow-zk/blob/main/lib/circuits/mdoc/zk_spec.cc) as a source of truth for the parameters
and convert it to CBOR/JSON as needed for corresponding protocols.**


## ZK Spec Parameters in ISO 18013-5

[ISO 18013-5 Second Edition](https://github.com/ISOWG10/ISO-18013/tree/main/Working%20Documents) section 10.2.7 defines `ZkSystemSpec` like this:

```
ZkSystemSpec = {
 "zkSystemId": ZkSystemId
 "system": ZkSystem,
 "params": ZkParams,
 * tstr => RFU
}

ZkSystem = tstr
ZkSystemId = tstr
ZkParams = { * tstr => Ext}
```

This is an example of a correctly filled `ZKSystemSpec`:
```
Spec1 = {
 "zkSystemId": "137e5a75ce72735a37c8a72da1a8a0a5df8d13365c2ae3d2c2bd6a0e7197c7c6"
 "system": "longfellow-libzk-v1",
 "params": {
   "circuit_hash":"137e5a75ce72735a37c8a72da1a8a0a5df8d13365c2ae3d2c2bd6a0e7197c7c6",
   "num_attributes": 1,
   "version": 6,
   "block_enc_hash": 4025,
   "block_enc_sig": 2945,
 }
}
```

## ZK Spec Parameters in OpenID4VP DCQL

Currently there is no standard DCQL for OpenID4VP. We recommend using [`mso_mdoc_zk`](https://longfellow-zk.github.io/longfellow-zk/docs/protocols/) format to request an ISO mDL via OpenId4VP. This is an example of a correctly filled `zk_system_type` for this type of request:
```
"zk_system_type": [
   {
     "id": "137e5a75ce72735a37c8a72da1a8a0a5df8d13365c2ae3d2c2bd6a0e7197c7c6"
     "system": "longfellow-libzk-v1",
     "circuit_hash":"137e5a75ce72735a37c8a72da1a8a0a5df8d13365c2ae3d2c2bd6a0e7197c7c6",
     "num_attributes": 1,
     "version": 6,
     "block_enc_hash": 4025,
     "block_enc_sig": 2945,
   }
 ],
```

