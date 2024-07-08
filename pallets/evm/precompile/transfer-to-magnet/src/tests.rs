// Copyright (C) Magnet.
// This file is part of Magnet.

// Magnet is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Magnet is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Magnet.  If not, see <http://www.gnu.org/licenses/>.

#![cfg(test)]

use super::*;

use crate::mock::*;
use frame_support::assert_ok;
use frame_support::traits::Currency;
use frame_system::RawOrigin;
use pallet_evm::{AddressMapping, CallInfo, Error, ExitError, ExitReason, Runner};

use codec::Encode;
use sp_core::H160;

struct MaxSize;
impl Get<u32> for MaxSize {
	fn get() -> u32 {
		256u32
	}
}

fn deploy_contract(caller: H160, bytecode_path: &str) -> H160 {
	let mut bytecode_str =
		std::fs::read_to_string(bytecode_path).expect("Unable to read bytecode file");
	log::info!("First 10 characters of bytecode: {}", &bytecode_str[..10]);

	bytecode_str.retain(|c| !c.is_whitespace());
	if bytecode_str.starts_with("0x") {
		if (bytecode_str.len() - 2) % 2 != 0 {
			panic!("Bytecode has an odd length, ensure it is a valid hex string.");
		}
		bytecode_str = bytecode_str[2..].to_string();
	} else if bytecode_str.len() % 2 != 0 {
		panic!("Bytecode has an odd length, ensure it is a valid hex string.");
	}

	let input = hex::decode(&bytecode_str).expect("Failed to decode hex bytecode");

	let gas_limit = 10000000u64;
	let value = U256::zero();

	let create_result = <Test as pallet_evm::Config>::Runner::create(
		caller,
		input,
		value,
		gas_limit,
		None,
		None,
		None,
		Vec::new(),
		false,
		true,
		None,
		None,
		<Test as pallet_evm::Config>::config(),
	)
	.expect("contract creation runs successfully");

	let balance = query_balance_of(create_result.value, caller, caller);
	log::info!("balance of caller:{:?}", balance);

	create_result.value
}

fn create_and_register_asset(erc20_address: H160) -> u32 {
	let asset_id = 3u32;
	let root_origin: frame_system::Origin<Test> = frame_system::RawOrigin::Root;
	let alice_balance = Balances::free_balance(&ALICE);
	log::info!("create and register asset -> alice balance:{:?}", alice_balance);

	let alice_origin: frame_system::Origin<Test> = frame_system::Origin::<Test>::Signed(ALICE);

	assert_ok!(Assets::force_create(
		root_origin.clone().into(),
		asset_id.into(),
		ALICE.into(),
		false,
		1u128.into()
	));
	assert_ok!(AssetsBridge::set_admin(root_origin.into(), ALICE));
	assert_ok!(AssetsBridge::register(alice_origin.clone().into(), asset_id, erc20_address));

	let bound_assets_id = pallet_assets_bridge::AssetIds::<Test>::get(erc20_address)
		.expect("Failed to get bound assets id.");
	log::info!("bound assets id succeed:{:?}", bound_assets_id);

	asset_id
}

fn create_without_register_asset() -> u32 {
	let asset_id = 3u32;
	let root_origin: frame_system::Origin<Test> = frame_system::RawOrigin::Root;
	let alice_balance = Balances::free_balance(&ALICE);
	log::info!("create assets without register asset -> alice balance:{:?}", alice_balance);

	assert_ok!(Assets::force_create(
		root_origin.clone().into(),
		asset_id.into(),
		ALICE.into(),
		false,
		1u128.into()
	));
	assert_ok!(AssetsBridge::set_admin(root_origin.into(), ALICE));

	asset_id
}

fn mint_erc20_tokens(erc20_address: H160, recipient: H160, amount: u128, origin: H160) {
	let selector_bytes: [u8; 4] = sp_io::hashing::keccak_256(b"mint(address,uint256)")[0..4]
		.try_into()
		.unwrap();

	let mint_selector = u32::from_be_bytes(selector_bytes);

	let recipient_encoded = recipient.to_fixed_bytes();
	let amount_encoded = solidity::encode_arguments(U256::from(amount));

	let mut input = mint_selector.to_be_bytes().to_vec();
	input.extend_from_slice(&[0u8; 12][..]);
	input.extend_from_slice(&recipient_encoded);
	input.extend_from_slice(&amount_encoded);
	log::info!("mint erc20 tokens input: {:?}", hex::encode(&input));

	let gas_limit = 10000000u64;

	let result = <Test as pallet_evm::Config>::Runner::call(
		origin.into(),
		erc20_address,
		input,
		U256::zero(),
		gas_limit,
		None,
		None,
		None,
		Vec::new(),
		false,
		true,
		None,
		None,
		<Test as pallet_evm::Config>::config(),
	);

	match &result {
		Ok(_) => log::info!("Minting tokens succeeded."),
		Err(e) => log::error!("Minting tokens failed: {:?}", e),
	}

	assert_ok!(result);
}

fn burn_erc20_tokens(
	token_address: H160,
	origin: H160,
	amount: u128,
	recipient: H160,
) -> Result<(), String> {
	// ABI-encoded function signature for `burn(address,uint256)`
	let burn_selector = sp_io::hashing::keccak_256(b"burn(address,uint256)")[..4].to_vec();
	let recipient_encoded = recipient.as_bytes().to_vec();
	let amount_encoded = solidity::encode_arguments(U256::from(amount));

	// Combine all parts into the full call data
	let mut call_data = Vec::new();
	call_data.extend_from_slice(&burn_selector);
	call_data.extend_from_slice(&[0u8; 12]); // padding for address
	call_data.extend_from_slice(&recipient_encoded);
	call_data.extend_from_slice(&amount_encoded);

	let result = <Test as pallet_evm::Config>::Runner::call(
		origin.into(),
		token_address,
		call_data,
		U256::zero(),
		1000000,
		None,
		None,
		None,
		Vec::new(),
		false,
		true,
		None,
		None,
		<Test as pallet_evm::Config>::config(),
	);

	match result {
		Ok(output) => {
			if !output.value.is_empty() {
				Ok(())
			} else {
				Err("Burn function returned empty value".to_string())
			}
		},
		Err(e) => Err(format!("Burn function call failed: {:?}", e)),
	}
}

fn query_balance_of(erc20_address: H160, account: H160, origin: H160) -> U256 {
	let selector_bytes: [u8; 4] =
		sp_io::hashing::keccak_256(b"balanceOf(address)")[0..4].try_into().unwrap();

	let account_encoded = account.to_fixed_bytes();

	let mut input = selector_bytes.to_vec();
	input.extend_from_slice(&[0u8; 12][..]);
	input.extend_from_slice(&account_encoded);
	log::info!("Query balance input: {:?}", hex::encode(&input));

	let gas_limit = 10000000u64;

	let result = <Test as pallet_evm::Config>::Runner::call(
		origin.into(),
		erc20_address,
		input,
		U256::zero(),
		gas_limit,
		None,
		None,
		None,
		Vec::new(),
		false,
		true,
		None,
		None,
		<Test as pallet_evm::Config>::config(),
	)
	.expect("EVM call BalanceOf failed.");

	U256::from_big_endian(&result.value)
}

fn query_allowance_of(
	token_address: H160,
	owner: H160,
	spender: H160,
) -> U256 {
	// ABI-encoded function signature for `allowance(address,address)`
	let allowance_selector = sp_io::hashing::keccak_256(b"allowance(address,address)")[..4].to_vec();
	let owner_encoded = owner.as_bytes().to_vec();
	let spender_encoded = spender.as_bytes().to_vec();

	// Combine all parts into the full call data
	let mut call_data = Vec::new();
	call_data.extend_from_slice(&allowance_selector);
	call_data.extend_from_slice(&[0u8; 12]); // padding for address
	call_data.extend_from_slice(&owner_encoded);
	call_data.extend_from_slice(&[0u8; 12]); // padding for address
	call_data.extend_from_slice(&spender_encoded);

	let result = <Test as pallet_evm::Config>::Runner::call(
		owner.into(),
		token_address,
		call_data,
		U256::zero(),
		1000000,
		None,
		None,
		None,
		Vec::new(),
		false,
		true,
		None,
		None,
		<Test as pallet_evm::Config>::config(),
	);

	match result {
		Ok(output) => {
			if !output.value.is_empty() {
				U256::from_big_endian(&output.value)
			} else {
				U256::zero()
			}
		},
		Err(_) => U256::zero(),
	}
}

#[test]
fn transfer_to_substrate_works() {
	env_logger::init();

	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		let bob_evm: H160 = H160([
			0x05, 0xF9, 0xb8, 0xC7, 0x6E, 0x89, 0x87, 0xB8, 0x15, 0xC9, 0x3C, 0x27, 0xD1, 0x45,
			0x20, 0xb6, 0xeD, 0x57, 0x39, 0x02,
		]);
		log::info!("bob evm:{:?}", bob_evm);

		let erc20_bytecode_path = "./contracts/StandardERC20_ByteCode.txt";
		let evm_bytecode_path = "./contracts/FixedEvmContract_ByteCode.txt";

		let bob = <Test as pallet_evm::Config>::AddressMapping::into_account_id(bob_evm);
		let _ = Balances::deposit_creating(&ALICE, 10_000_000_000_000_000_000);
		let _ = Balances::deposit_creating(&bob, 6_000_000_000_000_000_000);

		let (bob_evm_account, _) = EVM::account_basic(&bob_evm);
		let bob_evm_value_before: u128 = bob_evm_account.balance.as_u128();
		log::info!("bob evm value before:{:?}", bob_evm_value_before);

		let mint_amount: u128 = 1_000_000_000_000_000_000;
		let transfer_token_amount: u128 = 800_000_000_000_000_000;

		let alice_ss58_address = ALICE.to_ss58check();
		let alice_ss58_bstring = <BoundedString<MaxSize>>::from(alice_ss58_address);

		let token_addr = deploy_contract(bob_evm, erc20_bytecode_path);
		log::info!("token addr:{:?}", token_addr);

		let fixed_evm_contract = deploy_contract(bob_evm, evm_bytecode_path);
		log::info!("Fixed EVM contract addr:{:?}", fixed_evm_contract);

		let asset_id = create_and_register_asset(token_addr);
		log::info!("asset id:{:?}", asset_id);

		let admin_key = AccountId32::from([1u8; 32]);
		let root_origin: frame_system::Origin<Test> = frame_system::RawOrigin::Root;
		let _ =
			pallet_assets_bridge::Pallet::<Test>::set_admin(root_origin.into(), admin_key.clone());
		let r = pallet_assets_bridge::Pallet::<Test>::add_evm_contract(
			RawOrigin::Signed(admin_key.clone()).into(),
			bob_evm,
		);
		log::info!("add evm contract result:{:?}", r);

		let callers = pallet_assets_bridge::EvmContracts::<Test>::get();
		log::info!("callers:{:?}", callers);

		let alice_token_amount_before = Assets::balance(asset_id, &ALICE);
		log::info!("alice token amount before mint:{:?}", alice_token_amount_before);

		let bob_evm_token_before_mint: U256 = query_balance_of(token_addr, bob_evm, bob_evm);
		log::info!("before mint, bob evm token balance:{:?}", bob_evm_token_before_mint);
		mint_erc20_tokens(token_addr, bob_evm, mint_amount, bob_evm);
		let bob_evm_token_after_mint: U256 = query_balance_of(token_addr, bob_evm, bob_evm);
		log::info!("after mint, bob evm token balance:{:?}", bob_evm_token_after_mint);

		// approve FixedEvmContract transfer token
		let approve_selector_bytes: [u8; 4] =
			sp_io::hashing::keccak_256(b"approve(address,uint256)")[0..4]
				.try_into()
				.unwrap();
		let approve_selector = u32::from_be_bytes(approve_selector_bytes);
		let fixed_evm_contract_encoded = fixed_evm_contract.to_fixed_bytes();
		let amount_encoded = solidity::encode_arguments(U256::from(transfer_token_amount));
		let mut approve_call_data = approve_selector.to_be_bytes().to_vec();
		approve_call_data.extend_from_slice(&[0u8; 12][..]);
		approve_call_data.extend_from_slice(&fixed_evm_contract_encoded);
		approve_call_data.extend_from_slice(&amount_encoded);
		let gas_limit = 10000000u64;

		let call_result = <Test as pallet_evm::Config>::Runner::call(
			bob_evm.into(),
			token_addr,
			approve_call_data,
			U256::zero(),
			gas_limit,
			None,
			None,
			None,
			Vec::new(),
			false,
			true,
			None,
			None,
			<Test as pallet_evm::Config>::config(),
		);

		match call_result {
			Ok(_) => log::info!("Call to approve function succeeded."),
			Err(e) => log::error!("Call to approve function failed: {:?}", e),
		}

		// Check allowance
		let allowance = query_allowance_of(token_addr, bob_evm, fixed_evm_contract);
		log::info!("Allowance of fixedEvmContract: {:?}", allowance);

		// Check balance of bob_evm
		let bob_balance = query_balance_of(token_addr, bob_evm, bob_evm);
		log::info!("Balance of bob_evm: {:?}", bob_balance);

		// call FixedEvmContract TransferToMagnet()
		let selector_bytes: [u8; 4] =
			sp_io::hashing::keccak_256(b"transferToMagnet(address,uint256,string)")[0..4]
				.try_into()
				.unwrap();
		let selector = u32::from_be_bytes(selector_bytes);

		let transfer_value_encoded = solidity::encode_arguments(transfer_token_amount);
		let alice_ss58_address_encoded = solidity::encode_arguments(alice_ss58_bstring);
		let alice_ss58_address_len: u128 = alice_ss58_address_encoded.len().try_into().unwrap();
		let alice_ss58_address_len_encoded = solidity::encode_arguments(alice_ss58_address_len);
		log::info!("alice ss58 address encoded length:{:?}", alice_ss58_address_len);

		let mut call_data = selector.to_be_bytes().to_vec();
		call_data.extend_from_slice(&token_addr.as_bytes());
		call_data.extend_from_slice(&transfer_value_encoded);
		call_data.extend_from_slice(&alice_ss58_address_len_encoded);
		call_data.extend_from_slice(&alice_ss58_address_encoded);
		log::info!("transferToMagnet callData:{:?}", hex::encode(&call_data.clone()));

		let is_transactional = true;
		let validate = true;
		let call_result = <Test as pallet_evm::Config>::Runner::call(
			bob_evm,
			fixed_evm_contract,
			call_data,
			0.into(),
			3000000,
			Some(U256::from(1_000_000_000)),
			Some(U256::default()),
			None,
			Vec::new(),
			is_transactional,
			validate,
			None,
			None,
			<Test as pallet_evm::Config>::config(),
		);

		match call_result {
			Ok(CallInfo { exit_reason: ExitReason::Succeed(_), used_gas: gas, .. }) => {
				log::info!("Transfer to magnet succeed. used gas:{:?}", gas);
			},
			Ok(CallInfo { exit_reason: reason, value: err_value, .. }) => {
				log::error!("error : {:?}", std::str::from_utf8(&err_value));
				panic!("Call transferToMagnet failed!({:?})", reason);
			},
			Err(e) => {
				log::error!("Call to transferToMagnet failed: {:?}", e);
				panic!("Call transferToMagnet failed: {:?}", e);
			}
		};

		let alice_token_amount_after = Assets::balance(asset_id, &ALICE);
		log::info!("alice token amount after mint:{:?}", alice_token_amount_after);

		let bob_evm_token_after_burn: U256 = query_balance_of(token_addr, bob_evm, bob_evm);
		log::info!("after burn, bob evm token balance:{:?}", bob_evm_token_after_burn);

		assert_eq!(alice_token_amount_before + transfer_token_amount, alice_token_amount_after);
		assert_eq!(bob_evm_token_after_mint, bob_evm_token_after_burn + transfer_token_amount);
	})
}

/*
#[test]
fn gas_not_enough_error_works() {
	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		//let bob_evm= H160::from_slice(&[17u8;20][..]);
		let bob_evm: H160 = H160([
			0x05, 0xF9, 0xb8, 0xC7, 0x6E, 0x89, 0x87, 0xB8, 0x15, 0xC9, 0x3C, 0x27, 0xD1, 0x45,
			0x20, 0xb6, 0xeD, 0x57, 0x39, 0x02,
		]);
		log::info!("bob evm:{:?}", bob_evm);

		let erc20_bytecode_path = "./contracts/StandardERC20_ByteCode.txt";
		let evm_bytecode_path = "./contracts/FixedEvmContract_ByteCode.txt";

		let bob = <Test as pallet_evm::Config>::AddressMapping::into_account_id(bob_evm);
		let _ = Balances::deposit_creating(&ALICE, 10_000_000_000_000_000_000);
		let _ = Balances::deposit_creating(&bob, 6_000_000_000_000_000_000);

		let (bob_evm_account, _) = EVM::account_basic(&bob_evm);

		let bob_evm_value_before: u128 = bob_evm_account.balance.as_u128();
		log::info!("bob evm value before:{:?}", bob_evm_value_before);

		let mint_amount: u128 = 1000_000_000_000_000_000;
		let transfer_token_amount: u128 = 800_000_000_000_000_000;

		let target: H160 = H160::from_low_u64_be(2049);

		let alice_ss58_address = ALICE.to_ss58check();
		let alice_ss58_bstring = <BoundedString<MaxSize>>::from(alice_ss58_address);

		let token_addr = deploy_contract(bob_evm, erc20_bytecode_path);
		log::info!("token addr:{:?}", token_addr);

		let fixed_evm_contract = deploy_contract(bob_evm, evm_bytecode_path);
		log::info!("Fixed EVM contract addr:{:?}", fixed_evm_contract);

		let admin_key = AccountId32::from([1u8; 32]);
		let root_origin: frame_system::Origin<Test> = frame_system::RawOrigin::Root;
		let _ =
			pallet_assets_bridge::Pallet::<Test>::set_admin(root_origin.into(), admin_key.clone());
		let r = pallet_assets_bridge::Pallet::<Test>::add_evm_contract(
			RawOrigin::Signed(admin_key.clone()).into(),
			bob_evm,
		);
		log::info!("add evm contract result:{:?}", r);

		let callers = pallet_assets_bridge::EvmContracts::<Test>::get();
		log::info!("callers:{:?}", callers);

		let asset_id = create_and_register_asset(token_addr);
		log::info!("asset id:{:?}", asset_id);

		let alice_token_amount_before = Assets::balance(asset_id, &ALICE);
		log::info!("alice token amount before mint:{:?}", alice_token_amount_before);

		let bob_evm_token_before_mint: U256 = query_balance_of(token_addr, bob_evm, bob_evm);
		log::info!("before mint, bob evm token balance:{:?}", bob_evm_token_before_mint);
		mint_erc20_tokens(token_addr, bob_evm, mint_amount, bob_evm);
		let bob_evm_token_after_mint: U256 = query_balance_of(token_addr, bob_evm, bob_evm);
		log::info!("after mint, bob evm token balance:{:?}", bob_evm_token_after_mint);

		match burn_erc20_tokens(token_addr, bob_evm, transfer_token_amount, bob_evm) {
			Ok(_) => log::info!("Token burned."),
			Err(e) => {
				panic!("burn token execution reverted:{:?}.", e);
			},
		}

		let bob_evm_token_after_burn: U256 = query_balance_of(token_addr, bob_evm, bob_evm);
		log::info!("after burn, bob evm token balance:{:?}", bob_evm_token_after_burn);

		let selector_bytes: [u8; 4] =
			sp_io::hashing::keccak_256(b"transferToMagnet(address,uint256,string)")[0..4]
				.try_into()
				.unwrap();
		let selector = u32::from_be_bytes(selector_bytes);

		let token_addr_encoded = token_addr.to_fixed_bytes();
		let transfer_value_encoded = solidity::encode_arguments(transfer_token_amount);
		let alice_ss58_address_encoded = solidity::encode_arguments(alice_ss58_bstring);
		let alice_ss58_address_len: u128 = alice_ss58_address_encoded.len().try_into().unwrap();
		let alice_ss58_address_len_encoded = solidity::encode_arguments(alice_ss58_address_len);
		log::info!("alice ss58 address encoded length:{:?}", alice_ss58_address_len);

		let mut call_data = selector.to_be_bytes().to_vec();
		call_data.extend_from_slice(&[0u8; 12][..]);
		call_data.extend_from_slice(&token_addr_encoded);
		call_data.extend_from_slice(&transfer_value_encoded);
		call_data.extend_from_slice(&alice_ss58_address_len_encoded);
		call_data.extend_from_slice(&alice_ss58_address_encoded);
		log::info!("transferToMagnet callData:{:?}", hex::encode(&call_data.clone()));

		let is_transactional = true;
		let validate = true;
		let call_result = <Test as pallet_evm::Config>::Runner::call(
			bob_evm,
			target,
			call_data,
			0.into(),
			300,
			Some(U256::from(1_000_000_000)),
			Some(U256::default()),
			None,
			Vec::new(),
			is_transactional,
			validate,
			None,
			None,
			<Test as pallet_evm::Config>::config(),
		);
		assert!(call_result.is_err());
		let err = call_result.unwrap_err().error;
		log::info!("test gas limit too low err:{:?}", err);
		match err {
			Error::<Test>::GasLimitTooLow => assert!(true),
			_ => panic!("Not GasLimitTooLow but {:?}", err),
		}
	})
}
*/

/*
#[test]
fn gas_price_too_low_error_works() {
	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		//let bob_evm= H160::from_slice(&[17u8;20][..]);
		let bob_evm: H160 = H160([
			0x05, 0xF9, 0xb8, 0xC7, 0x6E, 0x89, 0x87, 0xB8, 0x15, 0xC9, 0x3C, 0x27, 0xD1, 0x45,
			0x20, 0xb6, 0xeD, 0x57, 0x39, 0x02,
		]);
		log::info!("bob evm:{:?}", bob_evm);

		let erc20_bytecode_path = "./contracts/StandardERC20_ByteCode.txt";
		let evm_bytecode_path = "./contracts/FixedEvmContract_ByteCode.txt";

		let bob = <Test as pallet_evm::Config>::AddressMapping::into_account_id(bob_evm);
		let _ = Balances::deposit_creating(&ALICE, 10_000_000_000_000_000_000);
		let _ = Balances::deposit_creating(&bob, 6_000_000_000_000_000_000);

		let (bob_evm_account, _) = EVM::account_basic(&bob_evm);

		let bob_evm_value_before: u128 = bob_evm_account.balance.as_u128();
		log::info!("bob evm value before:{:?}", bob_evm_value_before);

		let mint_amount: u128 = 1000_000_000_000_000_000;
		let transfer_token_amount: u128 = 800_000_000_000_000_000;

		let target: H160 = H160::from_low_u64_be(2049);

		let alice_ss58_address = ALICE.to_ss58check();
		let alice_ss58_bstring = <BoundedString<MaxSize>>::from(alice_ss58_address);

		let token_addr = deploy_contract(bob_evm, erc20_bytecode_path);
		log::info!("token addr:{:?}", token_addr);

		let fixed_evm_contract = deploy_contract(bob_evm, evm_bytecode_path);
		log::info!("Fixed EVM contract addr:{:?}", fixed_evm_contract);

		let admin_key = AccountId32::from([1u8; 32]);
		let root_origin: frame_system::Origin<Test> = frame_system::RawOrigin::Root;
		let _ =
			pallet_assets_bridge::Pallet::<Test>::set_admin(root_origin.into(), admin_key.clone());
		let r = pallet_assets_bridge::Pallet::<Test>::add_evm_contract(
			RawOrigin::Signed(admin_key.clone()).into(),
			bob_evm,
		);
		log::info!("add evm contract result:{:?}", r);

		let callers = pallet_assets_bridge::EvmContracts::<Test>::get();
		log::info!("callers:{:?}", callers);

		let asset_id = create_and_register_asset(token_addr);
		log::info!("asset id:{:?}", asset_id);

		let alice_token_amount_before = Assets::balance(asset_id, &ALICE);
		log::info!("alice token amount before mint:{:?}", alice_token_amount_before);

		let bob_evm_token_before_mint: U256 = query_balance_of(token_addr, bob_evm, bob_evm);
		log::info!("before mint, bob evm token balance:{:?}", bob_evm_token_before_mint);
		mint_erc20_tokens(token_addr, bob_evm, mint_amount, bob_evm);
		let bob_evm_token_after_mint: U256 = query_balance_of(token_addr, bob_evm, bob_evm);
		log::info!("after mint, bob evm token balance:{:?}", bob_evm_token_after_mint);

		match burn_erc20_tokens(token_addr, bob_evm, transfer_token_amount, bob_evm) {
			Ok(_) => log::info!("Tokens were successfully burned."),
			Err(e) => {
				panic!("burn token execution reverted:{:?}.", e);
			},
		}
		let bob_evm_token_after_burn: U256 = query_balance_of(token_addr, bob_evm, bob_evm);
		log::info!("after burn, bob evm token balance:{:?}", bob_evm_token_after_burn);

		let selector_bytes: [u8; 4] =
			sp_io::hashing::keccak_256(b"transferToMagnet(address,uint256,string)")[0..4]
				.try_into()
				.unwrap();
		let selector = u32::from_be_bytes(selector_bytes);

		let token_addr_encoded = token_addr.to_fixed_bytes();
		let transfer_value_encoded = solidity::encode_arguments(transfer_token_amount);
		let alice_ss58_address_encoded = solidity::encode_arguments(alice_ss58_bstring);
		let alice_ss58_address_len: u128 = alice_ss58_address_encoded.len().try_into().unwrap();
		let alice_ss58_address_len_encoded = solidity::encode_arguments(alice_ss58_address_len);
		log::info!("alice ss58 address encoded length:{:?}", alice_ss58_address_len);

		let mut call_data = selector.to_be_bytes().to_vec();
		call_data.extend_from_slice(&[0u8; 12][..]);
		call_data.extend_from_slice(&token_addr_encoded);
		call_data.extend_from_slice(&transfer_value_encoded);
		call_data.extend_from_slice(&alice_ss58_address_len_encoded);
		call_data.extend_from_slice(&alice_ss58_address_encoded);
		log::info!("transferToMagnet callData:{:?}", hex::encode(&call_data.clone()));

		let is_transactional = true;
		let validate = true;
		let call_result = <Test as pallet_evm::Config>::Runner::call(
			bob_evm,
			target,
			call_data,
			0.into(),
			3_000_000,
			Some(U256::from(1_000)),
			Some(U256::default()),
			None,
			Vec::new(),
			is_transactional,
			validate,
			None,
			None,
			<Test as pallet_evm::Config>::config(),
		);
		assert!(call_result.is_err());
		let err = call_result.unwrap_err().error;
		log::info!("test gas price too low err:{:?}", err);
		match err {
			Error::<Test>::GasPriceTooLow => assert!(true),
			_ => panic!("Not GasPriceTooLow but {:?}", err),
		}
	})
}
 */

/*
#[test]
fn balance_not_enough_error_works() {
	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		//let bob_evm= H160::from_slice(&[17u8;20][..]);
		let bob_evm: H160 = H160([
			0x05, 0xF9, 0xb8, 0xC7, 0x6E, 0x89, 0x87, 0xB8, 0x15, 0xC9, 0x3C, 0x27, 0xD1, 0x45,
			0x20, 0xb6, 0xeD, 0x57, 0x39, 0x02,
		]);
		log::info!("bob evm:{:?}", bob_evm);

		let erc20_bytecode_path = "./contracts/StandardERC20_ByteCode.txt";
		let evm_bytecode_path = "./contracts/FixedEvmContract_ByteCode.txt";

		let bob = <Test as pallet_evm::Config>::AddressMapping::into_account_id(bob_evm);
		let _ = Balances::deposit_creating(&ALICE, 10_000_000_000_000_000_000);
		let _ = Balances::deposit_creating(&bob, 6_000_000_000_000_000_000);

		let (bob_evm_account, _) = EVM::account_basic(&bob_evm);

		let bob_evm_value_before: u128 = bob_evm_account.balance.as_u128();
		log::info!("bob evm value before:{:?}", bob_evm_value_before);

		let mint_amount: u128 = 1000_000_000_000_000_000;
		let transfer_token_amount: u128 = 1800_000_000_000_000_000;

		let token_addr = deploy_contract(bob_evm, erc20_bytecode_path);
		log::info!("token addr:{:?}", token_addr);

		let fixed_evm_contract = deploy_contract(bob_evm, evm_bytecode_path);
		log::info!("Fixed EVM contract addr:{:?}", fixed_evm_contract);

		let asset_id = create_and_register_asset(token_addr);
		log::info!("asset id:{:?}", asset_id);

		let alice_token_amount_before = Assets::balance(asset_id, &ALICE);
		log::info!("alice token amount before mint:{:?}", alice_token_amount_before);

		let bob_evm_token_before_mint: U256 = query_balance_of(token_addr, bob_evm, bob_evm);
		log::info!("before mint, bob evm token balance:{:?}", bob_evm_token_before_mint);
		mint_erc20_tokens(token_addr, bob_evm, mint_amount, bob_evm);
		let bob_evm_token_after_mint: U256 = query_balance_of(token_addr, bob_evm, bob_evm);
		log::info!("after mint, bob evm token balance:{:?}", bob_evm_token_after_mint);

		match burn_erc20_tokens(token_addr, bob_evm, transfer_token_amount, bob_evm) {
			Ok(_) => panic!("transfer must revert."),
			Err(_) => {
				log::info!("burn token execution reverted.");
			},
		};
	})
}

#[test]
fn selector_error_works() {
	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		//let bob_evm= H160::from_slice(&[17u8;20][..]);
		let bob_evm: H160 = H160([
			0x05, 0xF9, 0xb8, 0xC7, 0x6E, 0x89, 0x87, 0xB8, 0x15, 0xC9, 0x3C, 0x27, 0xD1, 0x45,
			0x20, 0xb6, 0xeD, 0x57, 0x39, 0x02,
		]);
		log::info!("bob evm:{:?}", bob_evm);

		let erc20_bytecode_path = "./contracts/StandardERC20_ByteCode.txt";
		let evm_bytecode_path = "./contracts/FixedEvmContract_ByteCode.txt";

		let bob = <Test as pallet_evm::Config>::AddressMapping::into_account_id(bob_evm);
		let _ = Balances::deposit_creating(&ALICE, 10_000_000_000_000_000_000);
		let _ = Balances::deposit_creating(&bob, 6_000_000_000_000_000_000);

		let (bob_evm_account, _) = EVM::account_basic(&bob_evm);

		let bob_evm_value_before: u128 = bob_evm_account.balance.as_u128();
		log::info!("bob evm value before:{:?}", bob_evm_value_before);

		let mint_amount: u128 = 1000_000_000_000_000_000;
		let transfer_token_amount: u128 = 800_000_000_000_000_000;

		let target: H160 = H160::from_low_u64_be(2049);

		let alice_ss58_address = ALICE.to_ss58check();
		let alice_ss58_bstring = <BoundedString<MaxSize>>::from(alice_ss58_address);

		let token_addr = deploy_contract(bob_evm, erc20_bytecode_path);
		log::info!("token addr:{:?}", token_addr);

		let fixed_evm_contract = deploy_contract(bob_evm, evm_bytecode_path);
		log::info!("Fixed EVM contract addr:{:?}", fixed_evm_contract);

		let asset_id = create_and_register_asset(token_addr);
		log::info!("asset id:{:?}", asset_id);

		let alice_token_amount_before = Assets::balance(asset_id, &ALICE);
		log::info!("alice token amount before mint:{:?}", alice_token_amount_before);

		let bob_evm_token_before_mint: U256 = query_balance_of(token_addr, bob_evm, bob_evm);
		log::info!("before mint, bob evm token balance:{:?}", bob_evm_token_before_mint);
		mint_erc20_tokens(token_addr, bob_evm, mint_amount, bob_evm);
		let bob_evm_token_after_mint: U256 = query_balance_of(token_addr, bob_evm, bob_evm);
		log::info!("after mint, bob evm token balance:{:?}", bob_evm_token_after_mint);

		match burn_erc20_tokens(token_addr, bob_evm, transfer_token_amount, bob_evm) {
			Ok(_) => log::info!("Token burned."),
			Err(e) => {
				panic!("burn token execution reverted:{:?}.", e);
			},
		}

		let bob_evm_token_after_burn: U256 = query_balance_of(token_addr, bob_evm, bob_evm);
		log::info!("after burn, bob evm token balance:{:?}", bob_evm_token_after_burn);

		let selector_bytes: [u8; 4] =
			sp_io::hashing::keccak_256(b"111transferToMagnet(address,uint256,string)")[0..4]
				.try_into()
				.unwrap();
		let selector = u32::from_be_bytes(selector_bytes);

		let token_addr_encoded = token_addr.to_fixed_bytes();
		let transfer_value_encoded = solidity::encode_arguments(transfer_token_amount);
		let alice_ss58_address_encoded = solidity::encode_arguments(alice_ss58_bstring);
		let alice_ss58_address_len: u128 = alice_ss58_address_encoded.len().try_into().unwrap();
		let alice_ss58_address_len_encoded = solidity::encode_arguments(alice_ss58_address_len);
		log::info!("alice ss58 address encoded length:{:?}", alice_ss58_address_len);

		let mut call_data = selector.to_be_bytes().to_vec();
		call_data.extend_from_slice(&[0u8; 12][..]);
		call_data.extend_from_slice(&token_addr_encoded);
		call_data.extend_from_slice(&transfer_value_encoded);
		call_data.extend_from_slice(&alice_ss58_address_len_encoded);
		call_data.extend_from_slice(&alice_ss58_address_encoded);
		log::info!("transferToMagnet callData:{:?}", hex::encode(&call_data.clone()));

		let is_transactional = true;
		let validate = true;
		let call_result = <Test as pallet_evm::Config>::Runner::call(
			bob_evm,
			target,
			call_data,
			0.into(),
			3_000_000,
			Some(U256::from(1_000_000_000)),
			Some(U256::default()),
			None,
			Vec::new(),
			is_transactional,
			validate,
			None,
			None,
			<Test as pallet_evm::Config>::config(),
		);
		assert_ok!(&call_result);
		let call_result = call_result.unwrap();

		match call_result {
			CallInfo { exit_reason: ExitReason::Succeed(_), value: _, used_gas: _, .. } => {
				panic!("exit_reason must not Succeed!");
			},
			CallInfo { exit_reason: _, value: err_value, .. } => {
				let v = unsafe { String::from_utf8_unchecked(err_value.clone()) };
				log::info!("exit value:{:?}", v);
				assert_eq!(err_value, "Not find the selector error".as_bytes().to_owned());
			},
		};
	})
}

#[test]
fn ss58address_error_works() {
	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		//let bob_evm= H160::from_slice(&[17u8;20][..]);
		let bob_evm: H160 = H160([
			0x05, 0xF9, 0xb8, 0xC7, 0x6E, 0x89, 0x87, 0xB8, 0x15, 0xC9, 0x3C, 0x27, 0xD1, 0x45,
			0x20, 0xb6, 0xeD, 0x57, 0x39, 0x02,
		]);
		log::info!("bob evm:{:?}", bob_evm);

		let erc20_bytecode_path = "./contracts/StandardERC20_ByteCode.txt";
		let evm_bytecode_path = "./contracts/FixedEvmContract_ByteCode.txt";

		let bob = <Test as pallet_evm::Config>::AddressMapping::into_account_id(bob_evm);
		let _ = Balances::deposit_creating(&ALICE, 10_000_000_000_000_000_000);
		let _ = Balances::deposit_creating(&bob, 6_000_000_000_000_000_000);

		let (bob_evm_account, _) = EVM::account_basic(&bob_evm);

		let bob_evm_value_before: u128 = bob_evm_account.balance.as_u128();
		log::info!("bob evm value before:{:?}", bob_evm_value_before);

		let mint_amount: u128 = 1000_000_000_000_000_000;
		let transfer_token_amount: u128 = 800_000_000_000_000_000;

		let target: H160 = H160::from_low_u64_be(2049);

		//let alice_ss58_address = ALICE.to_ss58check();
		//let alice_ss58_bstring = <BoundedString<MaxSize>>::from(alice_ss58_address);
		let alice_ss58_bstring = <BoundedString<MaxSize>>::from("1234567890");

		let token_addr = deploy_contract(bob_evm, erc20_bytecode_path);
		log::info!("token addr:{:?}", token_addr);

		let fixed_evm_contract = deploy_contract(bob_evm, evm_bytecode_path);
		log::info!("Fixed EVM contract addr:{:?}", fixed_evm_contract);

		let admin_key = AccountId32::from([1u8; 32]);
		let root_origin: frame_system::Origin<Test> = frame_system::RawOrigin::Root;
		let _ =
			pallet_assets_bridge::Pallet::<Test>::set_admin(root_origin.into(), admin_key.clone());
		let r = pallet_assets_bridge::Pallet::<Test>::add_evm_contract(
			RawOrigin::Signed(admin_key.clone()).into(),
			bob_evm,
		);
		log::info!("add evm contract result:{:?}", r);

		let callers = pallet_assets_bridge::EvmContracts::<Test>::get();
		log::info!("callers:{:?}", callers);

		let asset_id = create_and_register_asset(token_addr);
		log::info!("asset id:{:?}", asset_id);

		let alice_token_amount_before = Assets::balance(asset_id, &ALICE);
		log::info!("alice token amount before mint:{:?}", alice_token_amount_before);

		let bob_evm_token_before_mint: U256 = query_balance_of(token_addr, bob_evm, bob_evm);
		log::info!("before mint, bob evm token balance:{:?}", bob_evm_token_before_mint);
		mint_erc20_tokens(token_addr, bob_evm, mint_amount, bob_evm);
		let bob_evm_token_after_mint: U256 = query_balance_of(token_addr, bob_evm, bob_evm);
		log::info!("after mint, bob evm token balance:{:?}", bob_evm_token_after_mint);

		match burn_erc20_tokens(token_addr, bob_evm, transfer_token_amount, bob_evm) {
			Ok(_) => log::info!("Token burned."),
			Err(e) => {
				panic!("burn token execution reverted:{:?}.", e);
			},
		}

		let bob_evm_token_after_burn: U256 = query_balance_of(token_addr, bob_evm, bob_evm);
		log::info!("after burn, bob evm token balance:{:?}", bob_evm_token_after_burn);

		let selector_bytes: [u8; 4] =
			sp_io::hashing::keccak_256(b"transferToMagnet(address,uint256,string)")[0..4]
				.try_into()
				.unwrap();
		let selector = u32::from_be_bytes(selector_bytes);

		let token_addr_encoded = token_addr.to_fixed_bytes();
		let transfer_value_encoded = solidity::encode_arguments(transfer_token_amount);
		let alice_ss58_address_encoded = solidity::encode_arguments(alice_ss58_bstring);
		let alice_ss58_address_len: u128 = alice_ss58_address_encoded.len().try_into().unwrap();
		let alice_ss58_address_len_encoded = solidity::encode_arguments(alice_ss58_address_len);
		log::info!("alice ss58 address encoded length:{:?}", alice_ss58_address_len);

		let mut call_data = selector.to_be_bytes().to_vec();
		call_data.extend_from_slice(&[0u8; 12][..]);
		call_data.extend_from_slice(&token_addr_encoded);
		call_data.extend_from_slice(&transfer_value_encoded);
		call_data.extend_from_slice(&alice_ss58_address_len_encoded);
		call_data.extend_from_slice(&alice_ss58_address_encoded);
		log::info!("transferToMagnet callData:{:?}", hex::encode(&call_data.clone()));

		let is_transactional = true;
		let validate = true;
		let call_result = <Test as pallet_evm::Config>::Runner::call(
			bob_evm,
			target,
			call_data,
			0.into(),
			3_000_000,
			Some(U256::from(1_000_000_000)),
			Some(U256::default()),
			None,
			Vec::new(),
			is_transactional,
			validate,
			None,
			None,
			<Test as pallet_evm::Config>::config(),
		);
		assert_ok!(&call_result);
		let call_result = call_result.unwrap();

		match call_result {
			CallInfo { exit_reason: ExitReason::Succeed(_), value: _, used_gas: _, .. } => {
				panic!("exit_reason must not Succeed!");
			},
			CallInfo { exit_reason: reason, value: _, .. } => {
				assert_eq!(
					reason,
					ExitReason::Error(ExitError::Other(std::borrow::Cow::Borrowed(
						"AccountId32 from ss58check(string) failed"
					)))
				);
			},
		};
	})
}

#[test]
fn not_evm_admin_works() {
	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		let bob_evm = H160::from_slice(&[17u8; 20][..]);
		/*
		let bob_evm: H160 = H160([
			0x05, 0xF9, 0xb8, 0xC7, 0x6E, 0x89, 0x87, 0xB8, 0x15, 0xC9, 0x3C, 0x27, 0xD1, 0x45,
			0x20, 0xb6, 0xeD, 0x57, 0x39, 0x02,
		]);
		 */
		log::info!("bob evm:{:?}", bob_evm);

		let erc20_bytecode_path = "./contracts/StandardERC20_ByteCode.txt";
		let evm_bytecode_path = "./contracts/FixedEvmContract_ByteCode.txt";

		let bob = <Test as pallet_evm::Config>::AddressMapping::into_account_id(bob_evm);
		let _ = Balances::deposit_creating(&ALICE, 10_000_000_000_000_000_000);
		let _ = Balances::deposit_creating(&bob, 6_000_000_000_000_000_000);

		let (bob_evm_account, _) = EVM::account_basic(&bob_evm);

		let bob_evm_value_before: u128 = bob_evm_account.balance.as_u128();
		log::info!("bob evm value before:{:?}", bob_evm_value_before);

		let mint_amount: u128 = 1000_000_000_000_000_000;
		let transfer_token_amount: u128 = 800_000_000_000_000_000;

		let target: H160 = H160::from_low_u64_be(2049);

		let alice_ss58_address = ALICE.to_ss58check();
		let alice_ss58_bstring = <BoundedString<MaxSize>>::from(alice_ss58_address);

		let token_addr = deploy_contract(bob_evm, erc20_bytecode_path);
		log::info!("token addr:{:?}", token_addr);

		let fixed_evm_contract = deploy_contract(bob_evm, evm_bytecode_path);
		log::info!("Fixed EVM contract addr:{:?}", fixed_evm_contract);

		let asset_id = create_and_register_asset(token_addr);
		log::info!("asset id:{:?}", asset_id);

		let alice_token_amount_before = Assets::balance(asset_id, &ALICE);
		log::info!("alice token amount before mint:{:?}", alice_token_amount_before);

		let bob_evm_token_before_mint: U256 = query_balance_of(token_addr, bob_evm, bob_evm);
		log::info!("before mint, bob evm token balance:{:?}", bob_evm_token_before_mint);
		mint_erc20_tokens(token_addr, bob_evm, mint_amount, bob_evm);
		let bob_evm_token_after_mint: U256 = query_balance_of(token_addr, bob_evm, bob_evm);
		log::info!("after mint, bob evm token balance:{:?}", bob_evm_token_after_mint);

		match burn_erc20_tokens(token_addr, bob_evm, transfer_token_amount, bob_evm) {
			Ok(_) => log::info!("Token burned."),
			Err(e) => {
				panic!("burn token execution reverted:{:?}.", e);
			},
		}

		let bob_evm_token_after_burn: U256 = query_balance_of(token_addr, bob_evm, bob_evm);
		log::info!("after burn, bob evm token balance:{:?}", bob_evm_token_after_burn);

		let selector_bytes: [u8; 4] =
			sp_io::hashing::keccak_256(b"transferToMagnet(address,uint256,string)")[0..4]
				.try_into()
				.unwrap();
		let selector = u32::from_be_bytes(selector_bytes);

		let token_addr_encoded = token_addr.to_fixed_bytes();
		let transfer_value_encoded = solidity::encode_arguments(transfer_token_amount);
		let alice_ss58_address_encoded = solidity::encode_arguments(alice_ss58_bstring);
		let alice_ss58_address_len: u128 = alice_ss58_address_encoded.len().try_into().unwrap();
		let alice_ss58_address_len_encoded = solidity::encode_arguments(alice_ss58_address_len);
		log::info!("alice ss58 address encoded length:{:?}", alice_ss58_address_len);

		let mut call_data = selector.to_be_bytes().to_vec();
		call_data.extend_from_slice(&[0u8; 12][..]);
		call_data.extend_from_slice(&token_addr_encoded);
		call_data.extend_from_slice(&transfer_value_encoded);
		call_data.extend_from_slice(&alice_ss58_address_len_encoded);
		call_data.extend_from_slice(&alice_ss58_address_encoded);
		log::info!("transferToMagnet callData:{:?}", hex::encode(&call_data.clone()));

		let is_transactional = true;
		let validate = true;
		let call_result = <Test as pallet_evm::Config>::Runner::call(
			bob_evm,
			target,
			call_data,
			0.into(),
			3_000_000,
			Some(U256::from(1_000_000_000)),
			Some(U256::default()),
			None,
			Vec::new(),
			is_transactional,
			validate,
			None,
			None,
			<Test as pallet_evm::Config>::config(),
		);
		assert_ok!(&call_result);
		let call_result = call_result.unwrap();

		match call_result {
			CallInfo { exit_reason: ExitReason::Succeed(_), value: _, used_gas: _, .. } => {
				panic!("exit_reason must not Succeed!");
			},
			CallInfo { exit_reason: reason, value: _, .. } => {
				assert_eq!(
					reason,
					ExitReason::Error(ExitError::Other(std::borrow::Cow::Borrowed(
						"Caller is not in the admin allow set"
					)))
				);
			},
		};
	})
}

#[test]
fn token_and_assets_not_bound_works() {
	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		//let bob_evm= H160::from_slice(&[17u8;20][..]);
		let bob_evm: H160 = H160([
			0x05, 0xF9, 0xb8, 0xC7, 0x6E, 0x89, 0x87, 0xB8, 0x15, 0xC9, 0x3C, 0x27, 0xD1, 0x45,
			0x20, 0xb6, 0xeD, 0x57, 0x39, 0x02,
		]);
		log::info!("bob evm:{:?}", bob_evm);

		let erc20_bytecode_path = "./contracts/StandardERC20_ByteCode.txt";
		let evm_bytecode_path = "./contracts/FixedEvmContract_ByteCode.txt";

		let bob = <Test as pallet_evm::Config>::AddressMapping::into_account_id(bob_evm);
		let _ = Balances::deposit_creating(&ALICE, 10_000_000_000_000_000_000);
		let _ = Balances::deposit_creating(&bob, 6_000_000_000_000_000_000);

		let (bob_evm_account, _) = EVM::account_basic(&bob_evm);

		let bob_evm_value_before: u128 = bob_evm_account.balance.as_u128();
		log::info!("bob evm value before:{:?}", bob_evm_value_before);

		let mint_amount: u128 = 1000_000_000_000_000_000;
		let transfer_token_amount: u128 = 800_000_000_000_000_000;

		let target: H160 = H160::from_low_u64_be(2049);

		let alice_ss58_address = ALICE.to_ss58check();
		let alice_ss58_bstring = <BoundedString<MaxSize>>::from(alice_ss58_address);

		let token_addr = deploy_contract(bob_evm, erc20_bytecode_path);
		log::info!("token addr:{:?}", token_addr);

		let fixed_evm_contract = deploy_contract(bob_evm, evm_bytecode_path);
		log::info!("Fixed EVM contract addr:{:?}", fixed_evm_contract);

		let admin_key = AccountId32::from([1u8; 32]);
		let root_origin: frame_system::Origin<Test> = frame_system::RawOrigin::Root;
		let _ =
			pallet_assets_bridge::Pallet::<Test>::set_admin(root_origin.into(), admin_key.clone());
		let r = pallet_assets_bridge::Pallet::<Test>::add_evm_contract(
			RawOrigin::Signed(admin_key.clone()).into(),
			bob_evm,
		);
		log::info!("add evm contract result:{:?}", r);

		let callers = pallet_assets_bridge::EvmContracts::<Test>::get();
		log::info!("callers:{:?}", callers);

		let asset_id = create_without_register_asset();
		log::info!("asset id:{:?}", asset_id);

		let alice_token_amount_before = Assets::balance(asset_id, &ALICE);
		log::info!("alice token amount before mint:{:?}", alice_token_amount_before);

		let bob_evm_token_before_mint: U256 = query_balance_of(token_addr, bob_evm, bob_evm);
		log::info!("before mint, bob evm token balance:{:?}", bob_evm_token_before_mint);
		mint_erc20_tokens(token_addr, bob_evm, mint_amount, bob_evm);
		let bob_evm_token_after_mint: U256 = query_balance_of(token_addr, bob_evm, bob_evm);
		log::info!("after mint, bob evm token balance:{:?}", bob_evm_token_after_mint);

		match burn_erc20_tokens(token_addr, bob_evm, transfer_token_amount, bob_evm) {
			Ok(_) => log::info!("Token burned."),
			Err(e) => {
				panic!("burn token execution reverted:{:?}.", e);
			},
		}

		let bob_evm_token_after_burn: U256 = query_balance_of(token_addr, bob_evm, bob_evm);
		log::info!("after burn, bob evm token balance:{:?}", bob_evm_token_after_burn);

		let selector_bytes: [u8; 4] =
			sp_io::hashing::keccak_256(b"transferToMagnet(address,uint256,string)")[0..4]
				.try_into()
				.unwrap();
		let selector = u32::from_be_bytes(selector_bytes);

		let token_addr_encoded = token_addr.to_fixed_bytes();
		let transfer_value_encoded = solidity::encode_arguments(transfer_token_amount);
		let alice_ss58_address_encoded = solidity::encode_arguments(alice_ss58_bstring);
		let alice_ss58_address_len: u128 = alice_ss58_address_encoded.len().try_into().unwrap();
		let alice_ss58_address_len_encoded = solidity::encode_arguments(alice_ss58_address_len);
		log::info!("alice ss58 address encoded length:{:?}", alice_ss58_address_len);

		let mut call_data = selector.to_be_bytes().to_vec();
		call_data.extend_from_slice(&[0u8; 12][..]);
		call_data.extend_from_slice(&token_addr_encoded);
		call_data.extend_from_slice(&transfer_value_encoded);
		call_data.extend_from_slice(&alice_ss58_address_len_encoded);
		call_data.extend_from_slice(&alice_ss58_address_encoded);
		log::info!("transferToMagnet callData:{:?}", hex::encode(&call_data.clone()));

		let is_transactional = true;
		let validate = true;
		let call_result = <Test as pallet_evm::Config>::Runner::call(
			bob_evm,
			target,
			call_data,
			0.into(),
			3_000_000,
			Some(U256::from(1_000_000_000)),
			Some(U256::default()),
			None,
			Vec::new(),
			is_transactional,
			validate,
			None,
			None,
			<Test as pallet_evm::Config>::config(),
		);
		assert_ok!(&call_result);
		let call_result = call_result.unwrap();

		match call_result {
			CallInfo { exit_reason: ExitReason::Succeed(_), value: _, used_gas: _, .. } => {
				panic!("exit_reason must not Succeed!");
			},
			CallInfo { exit_reason: reason, value: _, .. } => {
				assert_eq!(
					reason,
					ExitReason::Error(ExitError::Other(std::borrow::Cow::Borrowed(
						"Failed to get asset_id from token_addr"
					)))
				);
			},
		};
	})
}
*/
