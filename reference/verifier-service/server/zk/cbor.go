// Copyright 2025 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// This file contains the functions that parse and prepare the proof request
// for validation:
//
//  1. ZKDeviceResponse CBOR structure is parsed and validated, see the description
//     of the format below.
//  2. The signing certificate is validated against the set of trusted CA certificates
//  3. All arguments required to execute run_mdoc_verifier from Longfellow ZK library
//     are prepared (see VerifyRequest format)
//
// The parser supports both the ISO 18013-5 Second Edition ZKDocument.
// For more information about CBOR, COSE and other standards see
// https://github.com/ISOWG10/ISO-18013/tree/main/Working%20Documents
package zk

import (
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/x509"
	"encoding/hex"
	"encoding/pem"
	"errors"
	"fmt"
	"log"
	"time"

	"github.com/fxamacker/cbor/v2"
)

// Maximum distance between the holder-chosen proof timestamp and the server clock.
const TIMESTAMP_MAX_SKEW = 5 * time.Minute

// X5ChainIndex is the index of the x509 chain in the COSE_Sign1 unprotected header.
const X5ChainIndex = 33

type zkSpec struct {
	System string
	Params zkParam
}

type zkParam struct {
	Version       uint
	CircuitHash   string
	NumAttributes uint
}

// IssuerSigned represents the claims signed by the issuer.
type IssuerSigned map[string][]zkSignedItem

type zkSignedItem struct {
	ElementIdentifier string
	ElementValue      cbor.RawMessage
}

type zkDocument struct {
	DocType      string
	ZKSystemType zkSpec
	IssuerSigned IssuerSigned
	MsoX5chain   chainCoseSign1
	Timestamp    string
	Proof        []byte
}

type zkDeviceResponse struct {
	Version     string
	ZKDocuments [][]byte
	Status      uint
}

type chainCoseSign1 struct {
	_           struct{} `cbor:",toarray"`
	Protected   string
	Unprotected map[int][]byte
	Payload     string
	Signature   string
}

type zkDeviceResponseIso struct {
	Version     string
	ZKDocuments []zkDocumentIso
	Status      uint
}
type zkDocumentIso struct {
	DocumentData []byte
	Proof        []byte
}

type zkDocumentDataIso struct {
	DocType      string
	ZkSystemId   string
	IssuerSigned IssuerSigned
	MsoX5chain   any
	Timestamp    string
}

// LoadIssuerRootCA loads a set of PEM-encoded root CA certificates into the IssuerRoots pool.
func LoadIssuerRootCA(rootPem []byte) error {
	for len(rootPem) > 0 {
		block, rest := pem.Decode(rootPem)
		if block == nil {
			break
		}
		if block.Type == "CERTIFICATE" {
			cert, err := x509.ParseCertificate(block.Bytes)
			if err != nil {
				return fmt.Errorf("failed to parse certificate: %w", err)
			}
			log.Printf("adding Issuer CA %s", cert.Subject)
			IssuerRoots.AddCert(cert)
		}
		rootPem = rest
	}
	return nil
}

func getFirstCert(msoX5chain any) ([]byte, error) {
	switch v := msoX5chain.(type) {
	case []byte:
		return v, nil
	case [][]byte:
		if len(v) == 0 {
			return nil, errors.New("msoX5chain is an empty array of certificates")
		}
		return v[0], nil
	case []any:
		if len(v) == 0 {
			return nil, errors.New("msoX5chain is an empty array of certificates")
		}
		if cert, ok := v[0].([]byte); ok {
			return cert, nil
		}
		return nil, fmt.Errorf("unexpected element type in msoX5chain: %T", v[0])
	default:
		return nil, fmt.Errorf("unexpected type for MsoX5chain: %T", msoX5chain)
	}
}

func ProcessDeviceResponseISO(b []byte) (*VerifyRequest, error) {
	log.Printf("processing ZKDeviceResponse in ISO format")
	var dr zkDeviceResponseIso
	if err := cbor.Unmarshal(b, &dr); err != nil {
		return nil, fmt.Errorf("failed to unmarshal ISO ZkDeviceResponse: %w", err)
	}
	if len(dr.ZKDocuments) != 1 {
		return nil, fmt.Errorf("expected 1 zkdocument, got %d", len(dr.ZKDocuments))
	}
	var zkd = dr.ZKDocuments[0]

	var zkdata zkDocumentDataIso
	if err := cbor.Unmarshal(zkd.DocumentData, &zkdata); err != nil {
		return nil, fmt.Errorf("failed to unmarshal zkDocumentData: %w", err)
	}

	if err := validateRequestIso(&zkd, &zkdata); err != nil {
		return nil, err
	}

	x509chain, err := getFirstCert(zkdata.MsoX5chain)
	if err != nil {
		return nil, err
	}

	pkx, pky, err := validateIssuerKey(x509chain)
	if err != nil {
		return nil, err
	}

	namespace, attrs, err := extractAttributesIso(zkdata.IssuerSigned)
	if err != nil {
		return nil, err
	}

	namespaceList, idList, cborValList := buildAttributeLists(namespace, attrs)

	return &VerifyRequest{
		System:                LONGFELLOW_V1,
		CircuitID:             zkdata.ZkSystemId,
		Pkx:                   pkx,
		Pky:                   pky,
		Now:                   zkdata.Timestamp,
		DocType:               zkdata.DocType,
		AttributeNamespaceIDs: namespaceList,
		AttributeIDs:          idList,
		AttributeCborValues:   cborValList,
		Proof:                 zkd.Proof,
		Claims:                zkdata.IssuerSigned,
	}, nil
}

// ProcessDeviceResponse processes the CBOR-encoded device response and returns a VerifyRequest.
func ProcessDeviceResponse(b []byte) (*VerifyRequest, error) {
	var dr zkDeviceResponseIso
	if err := cbor.Unmarshal(b, &dr); err == nil {
		return ProcessDeviceResponseISO(b)
	}
	return nil, errors.ErrUnsupported
}

func extractAttributesIso(issuerSigned IssuerSigned) (string, []zkSignedItem, error) {
	if len(issuerSigned) != 1 {
		return "", nil, fmt.Errorf("expected 1 namespace, got %d", len(issuerSigned))
	}

	var namespace string
	for k := range issuerSigned {
		namespace = k
		break
	}

	attrs, ok := issuerSigned[namespace]
	if !ok {
		return "", nil, fmt.Errorf("cannot extract attributes from namespace %s", namespace)
	}
	return namespace, attrs, nil
}

func buildAttributeLists(namespace string, attrs []zkSignedItem) ([]string, []string, [][]byte) {
	namespaceList := make([]string, len(attrs))
	idList := make([]string, len(attrs))
	cborValList := make([][]byte, len(attrs))
	for i, attr := range attrs {
		namespaceList[i] = namespace
		idList[i] = attr.ElementIdentifier
		cborValList[i] = attr.ElementValue
	}
	return namespaceList, idList, cborValList
}

func validateRequestIso(doc *zkDocumentIso, zkdata *zkDocumentDataIso) error {
	if len(zkdata.ZkSystemId) == 0 {
		return fmt.Errorf("Missing ZkSystemId")
	}
	if len(zkdata.Timestamp) != TIMESTAMP_LEN {
		return fmt.Errorf("invalid timestamp length: got %d, want %d", len(zkdata.Timestamp), TIMESTAMP_LEN)
	}
	// The holder chooses the timestamp the proof is bound to, so it must be
	// close to the server clock or an expired credential would still verify.
	ts, err := time.Parse(time.RFC3339, zkdata.Timestamp)
	if err != nil {
		return fmt.Errorf("invalid timestamp: %w", err)
	}
	if d := time.Since(ts); d > TIMESTAMP_MAX_SKEW || d < -TIMESTAMP_MAX_SKEW {
		return fmt.Errorf("timestamp %s is outside the allowed %s skew from server time", zkdata.Timestamp, TIMESTAMP_MAX_SKEW)
	}
	if len(zkdata.DocType) == 0 {
		return errors.New("doctype is empty")
	}
	if len(doc.Proof) == 0 {
		return errors.New("proof is empty")
	}
	return nil
}

// Validate the issuer key by checking the following properties:
//  1. The msoX5chain can be parsed into a sequence of x509 certs
//  2. The first cert, i.e., the signer's cert, uses ECDSA keys with P256
//  3. The certificate chain verifies against the IssuerRoots.
func validateIssuerKey(x509b []byte) (string, string, error) {

	certs, err := x509.ParseCertificates(x509b)
	if err != nil {
		return "", "", fmt.Errorf("failed to parse certificates: %w", err)
	}
	if len(certs) < 1 {
		return "", "", errors.New("no certificates in x5chain")
	}

	signer := certs[0]
	log.Printf("Signer Subject:      %s\n", signer.Subject)
	log.Printf("Signer Issuer:       %s\n", signer.Issuer)
	log.Printf("Signer Serial Number: %s\n", signer.SerialNumber)

	if signer.PublicKeyAlgorithm != x509.ECDSA {
		return "", "", errors.New("only ECDSA signatures are supported")
	}

	ecdsaPK, ok := signer.PublicKey.(*ecdsa.PublicKey)
	if !ok || ecdsaPK.Curve != elliptic.P256() {
		return "", "", errors.New("signer public key is not ECDSA P256")
	}

	middle := x509.NewCertPool()
	for i := 1; i < len(certs); i++ {
		middle.AddCert(certs[i])
	}

	opts := x509.VerifyOptions{
		Intermediates: middle,
		Roots:         IssuerRoots,
		KeyUsages:     []x509.ExtKeyUsage{x509.ExtKeyUsageAny},
	}

	if _, err := certs[0].Verify(opts); err != nil {
		for _, cert := range certs {
			log.Printf("cert subject: %v", cert.Subject)
		}
		return "", "", fmt.Errorf("failed to verify certificate chain: %w", err)
	}

	pkx := fmt.Sprintf("0x%s", hex.EncodeToString(ecdsaPK.X.Bytes()))
	pky := fmt.Sprintf("0x%s", hex.EncodeToString(ecdsaPK.Y.Bytes()))

	return pkx, pky, nil
}
