// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "@openzeppelin/contracts/token/ERC20/ERC20.sol";
import "@openzeppelin/contracts/access/Ownable.sol";
import "@openzeppelin/contracts/security/ReentrancyGuard.sol";

contract StandardERC20 is ERC20, Ownable {
    constructor(string memory name_, string memory symbol_) ERC20(name_, symbol_) Ownable(msg.sender) {}

    function mint(address to, uint256 amount) public onlyOwner {
        _mint(to, amount);
    }

    function burn(address from, uint256 amount) public onlyOwner {
        _burn(from, amount);
    }
}

interface ITransferToMagnet {
    function transferToMagnet(address tokenAddress, uint256 amount, string calldata ss58Address) external;
}

contract TransferToMagnet is Ownable, ReentrancyGuard {
    address private constant PRECOMPILE_ADDRESS = 0x0000000000000000000000000000000000000801;

    event TokensBurned(address indexed from, uint256 amount);
    event PrecompileCalled(address indexed caller, uint256 amount, string ss58Address);

    constructor() Ownable(msg.sender) {}

    function transferToMagnet(address tokenAddress, uint256 amount, string calldata ss58Address) external nonReentrant {
        StandardERC20 erc20Token = StandardERC20(tokenAddress);

        require(erc20Token.allowance(msg.sender, address(this)) >= amount, "Insufficient allowance");

        // Transfer tokens from user to this contract
        require(erc20Token.transferFrom(msg.sender, address(this), amount), "Transfer failed");

        // Burn the tokens
        erc20Token.burn(address(this), amount);
        emit TokensBurned(msg.sender, amount);

        // Call the precompile contract
        bytes4 selector = bytes4(keccak256("transferToMagnet(address,uint256,string)"));
        bytes memory data = abi.encodeWithSelector(selector, address(tokenAddress), amount, ss58Address);

        (bool success, ) = PRECOMPILE_ADDRESS.call(data);
        require(success, "Call to precompile failed");

        emit PrecompileCalled(msg.sender, amount, ss58Address);
    }
}
