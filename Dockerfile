# To build: 
#     docker build -t deugniets .
# To run:
#     docker run -d --rm --network host --name deugniets deugniets
#
FROM python:alpine
RUN apk upgrade --update && apk add --no-cache tzdata && cp /usr/share/zoneinfo/Europe/Amsterdam /etc/localtime && apk del tzdata
RUN apk add --no-cache --virtual build-dependencies build-base gcc openssl-dev libffi-dev git
EXPOSE 53/udp
ADD *.py *.docker ./
RUN pip3 install --upgrade pip cachetools chardet==3.0.4 urllib3==1.25.7 cryptography geoip2 idna IPy netaddr pygtrie python-hosts pytricia regex git+https://github.com/psf/requests@master git+https://github.com/rthalley/dnspython@master git+https://github.com/opendns/dnspython-clientsubnetoption@master
RUN apk del build-dependencies build-base gcc libffi-dev git
CMD [ "python3", "deugniets.py", "deugniets.conf.docker" ]
