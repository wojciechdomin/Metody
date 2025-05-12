if [ -z "$1" ]; then

    echo -e "\e[31mJak tego talatajstwa uzyc?"
    echo -e "\e[33mOtoz: chmod +x wyprobuj.sh ,a potem :"
    echo -e "\e[93m./wyprobuj.sh <wyrazenie w cudzyslowie>"
    echo -e "\e[92mewentualnie: bash wyprobuj.sh <wyrazenie w cudzyslowie>"
    echo -e "\e[94mrobi to:"
    echo -e "\e[0m"
    cat wyprobuj.sh
    exit 0
fi

echo "$1" > my.fun; dune exec func my.fun > my.c; gcc my.c -o my && ./my
