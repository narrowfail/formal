Powershell.exe -executionpolicy remotesigned "get-childitem -include *.dfy -recurse | foreach ($_) {dafny $_.fullname}"